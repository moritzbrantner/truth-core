/-
Report which propositional hypotheses of advertised result theorems the proof
term never uses (#571).

Usage, after `lake build`:

    lake env lean --run scripts/UnusedPremises.lean <input.json>

`<input.json>` is the input of `scripts/BindTypes.lean`
(`{"modules": [...], "theorems": [...], "bundle_prefixes": [...]}`). For each
theorem the tool opens the type with `forallTelescope` (as BindTypes does, so
binder positions agree), applies the proof term to those variables, and
traverses the result. It prints one JSON object per theorem listing every
propositional binder with its position, name and `used` flag; a theory bundle
binder (head in `bundle_prefixes`) also lists, per conjunct of its one-step
unfolding split on `∧`, whether that conjunct is used.

Usage is syntactic occurrence in the proof term, refined in three ways so that
a hypothesis that is only passed along and then dropped is not counted:

* `And.left`/`And.right`/`.1`/`.2` projections and `And.casesOn`/`And.rec`
  destructuring (which `obtain ⟨_, h, _⟩ := hBundle` elaborates to) are
  followed, so a bundle conjunct counts as used only if its component is;
* `match` auxiliaries are unfolded and beta-reduced, for the same reason;
* an argument passed to a `TruthCore` theorem counts only when that theorem's
  own proof uses the corresponding parameter (computed recursively, memoized);
* a `let`/`have` whose bound variable does not occur in the body is skipped.

Everything else is conservative: any other occurrence, including a whole
bundle passed to a helper or occurrence in a type annotation, counts as use.
So an "unused" report is a fact about the proof term; a "used" report does not
show that the hypothesis is logically needed.
-/
import Lean

open Lean Meta

/-- A tracked free variable stands for a target (binder index) and a path of
`∧` projections into it (`false` = left, `true` = right). -/
abbrev Use := Nat × List Bool

structure St where
  masks : Std.HashMap Name (Array Bool) := {}
  inProgress : Std.HashSet Name := {}
  /-- Subterms already visited by the current `analyze`. Each tracked variable
  keeps one origin for its lifetime (fresh variables are never re-tracked), so
  a subterm's contribution does not depend on where it is visited. -/
  seen : Std.HashSet Expr := {}

abbrev M := StateRefT St MetaM

def headConst? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => some n
  | _ => none

def isBundle (prefixes : Array String) (e : Expr) : Bool :=
  match headConst? e with
  | some n => prefixes.any fun p => p.isPrefixOf n.toString
  | none => false

/-- Leaf paths of a right- or left-nested conjunction, matching BindTypes' `splitAnd`. -/
partial def andLeaves (e : Expr) (path : List Bool) : Array (List Bool) :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    andLeaves e.appFn!.appArg! (path ++ [false]) ++ andLeaves e.appArg! (path ++ [true])
  else #[path]

def bundleLeaves (ty : Expr) : MetaM (Option (Array (List Bool))) := do
  match ← unfoldDefinition? ty.consumeMData with
  | some e => return some (andLeaves (← instantiateMVars e).headBeta [])
  | none => return none

def isTruthCore (n : Name) : Bool :=
  n.toString.startsWith "TruthCore."

mutual

/-- Which parameters (by position) the proof of theorem `c` uses. `none` when
`c` is not a `TruthCore` theorem with a value: then every argument counts. -/
partial def paramMask (c : Name) : M (Option (Array Bool)) := do
  if !isTruthCore c then return none
  if let some m := (← get).masks[c]? then return some m
  if (← get).inProgress.contains c then return none
  let some (.thmInfo info) := (← getEnv).find? c | return none
  modify fun s => { s with inProgress := s.inProgress.insert c }
  let mask ← forallTelescope info.type fun xs _ => do
    let tracked : Std.HashMap FVarId Use :=
      xs.foldl (init := {}) fun (m : Std.HashMap FVarId Use) x => m.insert x.fvarId! (m.size, [])
    let used ← analyze tracked (mkAppN (info.value.instantiateLevelParams info.levelParams
      (info.levelParams.map mkLevelParam)) xs).headBeta
    return (List.range xs.size).toArray.map fun i => used.any (·.1 == i)
  modify fun s => { s with masks := s.masks.insert c mask, inProgress := s.inProgress.erase c }
  return some mask

/-- All origins used in `e`. -/
partial def analyze (tracked : Std.HashMap FVarId Use) (e : Expr) : M (Array Use) := do
  let out ← IO.mkRef (#[] : Array Use)
  let saved := (← get).seen
  modify fun s => { s with seen := {} }
  visit tracked out e
  modify fun s => { s with seen := saved }
  out.get

/-- Resolve a projection chain ending in a tracked variable. -/
partial def resolve (tracked : Std.HashMap FVarId Use) (e : Expr) : Option Use :=
  let e := e.consumeMData
  match e with
  | .fvar f => tracked[f]?
  | .proj ``And i x => (resolve tracked x).map fun (t, p) => (t, p ++ [i == 1])
  | _ =>
    if e.isAppOfArity ``And.left 3 then
      (resolve tracked e.appArg!).map fun (t, p) => (t, p ++ [false])
    else if e.isAppOfArity ``And.right 3 then
      (resolve tracked e.appArg!).map fun (t, p) => (t, p ++ [true])
    else none

/-- Destructure `minor : ∀ left right, …` against a tracked conjunction. -/
partial def visitMinor (tracked : Std.HashMap FVarId Use) (out : IO.Ref (Array Use))
    (origin : Use) (minor : Expr) : M Unit := do
  match minor.consumeMData with
  | .lam n1 t1 (.lam n2 t2 body bi2) bi1 =>
    visit tracked out t1
    withLocalDecl n1 bi1 t1 fun l => do
      let t2 := t2.instantiate1 l
      visit tracked out t2
      withLocalDecl n2 bi2 t2 fun r => do
        let tracked := tracked.insert l.fvarId! (origin.1, origin.2 ++ [false])
          |>.insert r.fvarId! (origin.1, origin.2 ++ [true])
        visit tracked out (body.instantiateRev #[l, r])
  | _ =>
    out.modify (·.push origin)
    visit tracked out minor

partial def visit (tracked : Std.HashMap FVarId Use) (out : IO.Ref (Array Use)) (e : Expr) :
    M Unit := do
  if !e.hasFVar then return
  if (← get).seen.contains e then return
  modify fun s => { s with seen := s.seen.insert e }
  match e with
  | .mdata _ b => visit tracked out b
  | .fvar f => if let some o := tracked[f]? then out.modify (·.push o)
  | .proj _ _ x =>
    match resolve tracked e with
    | some o => out.modify (·.push o)
    | none => visit tracked out x
  | .lam n t b bi | .forallE n t b bi =>
    visit tracked out t
    withLocalDecl n bi t fun x => visit tracked out (b.instantiate1 x)
  | .letE n t v b _ =>
    visit tracked out t
    if !b.hasLooseBVar 0 then
      visit tracked out b
    else
      let tracked' := match resolve tracked v with
        | some o => some o
        | none => none
      if tracked'.isNone then visit tracked out v
      withLetDecl n t v fun x => do
        let tracked := match tracked' with
          | some o => tracked.insert x.fvarId! o
          | none => tracked
        visit tracked out (b.instantiate1 x)
  | .app .. => visitApp tracked out e
  | _ => pure ()

partial def visitApp (tracked : Std.HashMap FVarId Use) (out : IO.Ref (Array Use)) (e : Expr) :
    M Unit := do
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  -- Projection chain, possibly applied further (a conjunct that is a ∀).
  if fn.isConstOf ``And.left || fn.isConstOf ``And.right then
    if args.size ≥ 3 then
      if let some o := resolve tracked (mkAppN fn args[:3]) then
        out.modify (·.push o)
        for a in args[3:] do visit tracked out a
        return
  -- `And.casesOn {a b motive} t minor` and `And.rec {a b motive} minor t`.
  if (fn.isConstOf ``And.casesOn || fn.isConstOf ``And.rec) && args.size ≥ 5 then
    let (major, minor) := if fn.isConstOf ``And.casesOn then (args[3]!, args[4]!) else (args[4]!, args[3]!)
    if let some o := resolve tracked major then
      for a in args[:3] do visit tracked out a
      visitMinor tracked out o minor
      for a in args[5:] do visit tracked out a
      return
  -- Beta-redex `(fun x => b) v` with `x` unused in `b`.
  if let .lam _ _ b _ := fn then
    if args.size ≥ 1 && !b.hasLooseBVar 0 then
      visit tracked out (mkAppN b args[1:])
      return
    visit tracked out (fn.beta args)
    return
  if let .const c _ := fn then
    -- `match` auxiliaries: unfold and beta-reduce, then analyze the body.
    if (← Meta.isMatcher c) then
      if let some e' ← unfoldDefinition? e then
        let e' := e'.headBeta
        if e' != e then
          visit tracked out e'
          return
    if let some mask ← paramMask c then
      for h : i in [:args.size] do
        if i < mask.size && !mask[i]! then continue
        visit tracked out args[i]
      return
  visit tracked out fn
  for a in args do visit tracked out a

end

def covered (leaf : List Bool) (uses : Array (List Bool)) : Bool :=
  uses.any fun p => p.isPrefixOf leaf || leaf.isPrefixOf p

def describeTheorem (prefixes : Array String) (thm : Name) : M Json := do
  let some (.thmInfo info) := (← getEnv).find? thm
    | return Json.mkObj [("theorem", Json.str thm.toString), ("error", Json.str "unknown theorem")]
  if (← IO.getEnv "UNUSED_PREMISES_TRACE").isSome then IO.eprintln thm
  forallTelescope info.type fun xs _ => do
    let tracked : Std.HashMap FVarId Use :=
      xs.foldl (init := {}) fun (m : Std.HashMap FVarId Use) x => m.insert x.fvarId! (m.size, [])
    let value := info.value.instantiateLevelParams info.levelParams (info.levelParams.map mkLevelParam)
    let used ← analyze tracked (mkAppN value xs).headBeta
    let mut binders : Array Json := #[]
    for i in [:xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      if !(← isProp decl.type) then continue
      let uses := (used.filter (·.1 == i)).map (·.2)
      let mut d := Json.mkObj [
        ("position", toJson i),
        ("name", Json.str decl.userName.eraseMacroScopes.toString),
        ("used", Json.bool !uses.isEmpty)
      ]
      if isBundle prefixes decl.type then
        match ← bundleLeaves decl.type with
        | some leaves => d := d.mergeObj (Json.mkObj [("conjuncts_used", toJson (leaves.map (covered · uses)))])
        | none => d := d.mergeObj (Json.mkObj [("conjuncts_used", Json.str "cannot unfold")])
      binders := binders.push d
    return Json.mkObj [("theorem", Json.str thm.toString), ("hypotheses", Json.arr binders)]

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/UnusedPremises.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let theorems ← IO.ofExcept (input.getObjValAs? (Array String) "theorems")
  let prefixes := (input.getObjValAs? (Array String) "bundle_prefixes").toOption.getD #[]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<unused-premises>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let run : M (Array Json) := theorems.mapM fun t => describeTheorem prefixes t.toName
  let (out, _) ← ((run.run' {}).run').toIO ctx state
  IO.println (Json.arr out).compress
  return 0
