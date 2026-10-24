/-
Emit the binder structure of advertised result theorems as JSON (#162).

Usage, after `lake build`:

    lake env lean --run scripts/BindTypes.lean <input.json>

`<input.json>` is `{"modules": [...], "theorems": [...]}`. The tool imports the
modules, reads each theorem's type with `forallTelescope` (no reduction), and
prints one JSON object per theorem: every binder with its name, whether its
type lives in `Prop` (a propositional hypothesis) or not (a type or vocabulary
parameter), and the head constant of that type; then the same for the result
type. `scripts/corpus.py bind-check` compares this with the corpus records.

Head constants are read syntactically (`getAppFn` after stripping metadata).
Nothing is unfolded, so a `…Reading` definition applied to arguments reports
that definition. Logical wrappers the corpus may use around a declaration are
peeled and listed separately: `¬` (`Not`) and `∃` (`Exists`).

Theory bundles (#160). The input may list `bundle_prefixes`, namespaces of
theory definitions (for example `TruthCore.Comparison.`). A propositional
binder whose head is such a definition is additionally unfolded exactly one
step and split on `∧`; its conjuncts are listed under `bundle`. They are not
unfolded further, so a conjunct that is itself a theory definition stays one
item. For the result type, a theory definition is unfolded one step, leading
`∃` binders are opened, the body is split on `∧`, and each conjunct that is a
theory definition is unfolded one step and split again: this lists the
commitments of a consistency claim such as `∃ s, Background s ∧ Catholic s`.
-/
import Lean

open Lean Meta

/-- Strip metadata and return the head constant of `e`, if any. -/
def headConst? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => some n
  | _ => none

/-- Peel `Not` and `Exists` wrappers. Returns the wrappers (outermost first)
and the head constant of the innermost proposition. -/
partial def peel (e : Expr) (acc : Array String) : MetaM (Array String × Option Name) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    peel e.appArg! (acc.push "Not")
  else if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi =>
      withLocalDecl n bi ty fun x => peel (body.instantiate1 x) (acc.push "Exists")
    | _ => return (acc.push "Exists", none)
  else
    return (acc, headConst? e)

def nameJson : Option Name → Json
  | some n => Json.str n.toString
  | none => Json.null

/-- Describe one type: its sort class, raw head, peeled wrappers and core head. -/
def describeType (ty : Expr) : MetaM Json := do
  let ty ← instantiateMVars ty
  let sort ← whnf (← inferType ty)
  let isProp := sort.isProp
  let (wrappers, core) ← peel ty #[]
  let pp ← ppExpr ty
  return Json.mkObj [
    ("prop", Json.bool isProp),
    ("head", nameJson (headConst? ty)),
    ("wrappers", toJson wrappers),
    ("core_head", nameJson core),
    ("type", Json.str (toString pp))
  ]

def isBundle (prefixes : Array String) (e : Expr) : Bool :=
  match headConst? e with
  | some n => prefixes.any fun p => p.isPrefixOf n.toString
  | none => false

/-- Split a right-nested conjunction into its conjuncts. -/
partial def splitAnd (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then splitAnd e.appFn!.appArg! ++ splitAnd e.appArg! else #[e]

/-- Unfold the head definition of `e` exactly one step and beta-reduce. -/
def unfoldOnce (e : Expr) : MetaM (Option Expr) := do
  match ← unfoldDefinition? e.consumeMData with
  | some e' => return some (← instantiateMVars e').headBeta
  | none => return none

/-- The conjuncts of a theory bundle, one unfolding step deep. -/
def bundleConjuncts (e : Expr) : MetaM (Option (Array Expr)) := do
  return (← unfoldOnce e).map splitAnd

/-- Open leading `∃` binders and continue with the body. -/
partial def openExists (e : Expr) (k : Expr → MetaM Json) : MetaM Json := do
  let e := e.consumeMData
  if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi => withLocalDecl n bi ty fun x => openExists (body.instantiate1 x) k
    | _ => k e
  else k e

def describeConjuncts (cs : Array Expr) : MetaM Json := do
  return Json.arr (← cs.mapM describeType)

/-- Bundle description of a hypothesis type, if its head is a theory definition. -/
def hypothesisBundle (prefixes : Array String) (ty : Expr) : MetaM (Option Json) := do
  if !isBundle prefixes ty then return none
  match ← bundleConjuncts ty with
  | some cs => return some (← describeConjuncts cs)
  | none => return some (Json.str "cannot unfold")

/-- Commitments of a result type whose head is a theory definition. -/
def resultBundle (prefixes : Array String) (ty : Expr) : MetaM (Option Json) := do
  if !isBundle prefixes ty then return none
  let some body ← unfoldOnce ty | return some (Json.str "cannot unfold")
  let items ← openExists body fun inner => do
    let mut out : Array Expr := #[]
    for c in splitAnd inner do
      if isBundle prefixes c then
        match ← bundleConjuncts c with
        | some cs => out := out ++ cs
        | none => out := out.push c
      else
        out := out.push c
    describeConjuncts out
  return some items

def describeTheorem (prefixes : Array String) (thm : Name) : MetaM Json := do
  let some info := (← getEnv).find? thm
    | return Json.mkObj [("theorem", Json.str thm.toString), ("error", Json.str "unknown constant")]
  forallTelescope info.type fun xs body => do
    let mut binders : Array Json := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let mut d ← describeType decl.type
      if ← isProp decl.type then
        if let some b ← hypothesisBundle prefixes decl.type then
          d := d.mergeObj (Json.mkObj [("bundle", b)])
      binders := binders.push (d.mergeObj (Json.mkObj [("name", Json.str decl.userName.eraseMacroScopes.toString)]))
    let mut result ← describeType body
    if let some b ← resultBundle prefixes body then
      result := result.mergeObj (Json.mkObj [("bundle", b)])
    return Json.mkObj [
      ("theorem", Json.str thm.toString),
      ("binders", Json.arr binders),
      ("result", result)
    ]

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/BindTypes.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let theorems ← IO.ofExcept (input.getObjValAs? (Array String) "theorems")
  let prefixes := (input.getObjValAs? (Array String) "bundle_prefixes").toOption.getD #[]
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<bind-types>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (MetaM.run' (theorems.mapM fun t => describeTheorem prefixes t.toName)).toIO ctx state
  IO.println (Json.arr out).compress
  return 0
