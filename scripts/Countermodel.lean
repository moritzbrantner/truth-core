import Lean
/-!
First-order skeleton of a theorem for the omission-countermodel finder
(`scripts/countermodel.py`, docs/countermodels.md).

Usage, after `lake build <module>`:

    lake env lean --run scripts/Countermodel.lean <input.json>

Input: `{"modules": [...], "theorem": "<name>"}`. The theorem's binders are
classified as carriers (`B : Type` or `Sort u`), predicate parameters (functions
from carriers, or from carrier-valued predicates `T → Prop`, into `Prop`),
element constants (`esse : R`) and propositional hypotheses (premises). Each
premise and the conclusion are unfolded through definitions into a formula over
`∀ ∃ ∧ ∨ ¬ → ↔ = ≠ True False` and predicate atoms; quantifiers over `Prop`
(as in `ExcludedMiddle`) range over the two truth values. The output is a search
problem, never a verdict: a model the finder proposes is checked again by Lean.
Anything outside this fragment is reported as an `error` naming the offending
expression.
-/
open Lean Meta

namespace Countermodel

def str (s : String) : Json := Json.str s

structure Ctx where
  /-- Carrier free variables and their names. -/
  carriers : Array (FVarId × String) := #[]
  /-- Predicate parameters, element constants and bound variables. -/
  names : Array (FVarId × String) := #[]

structure St where
  unfolded : Array Name := #[]
  counter : Nat := 0

abbrev M := StateRefT St MetaM

def lookup (xs : Array (FVarId × String)) (f : FVarId) : Option String :=
  (xs.find? (·.1 == f)).map (·.2)

def fresh (base : Name) : M String := do
  let n ← modifyGet fun s => (s.counter, { s with counter := s.counter + 1 })
  let b := base.eraseMacroScopes.toString
  return s!"{if b.isEmpty then "x" else b}#{n}"

def carrierOf (ctx : Ctx) (ty : Expr) : Option String :=
  match ty.consumeMData with
  | .fvar f => lookup ctx.carriers f
  | _ => none

/-- A sort: a carrier name, or `{"set": [carriers]}` for `T₁ → … → Tₙ → Prop`. -/
def sortOf (ctx : Ctx) (ty : Expr) : MetaM (Option Json) := do
  if let some c := carrierOf ctx ty then return some (str c)
  forallTelescope ty fun xs body => do
    if xs.isEmpty || !body.consumeMData.isProp then return none
    let mut cs : Array Json := #[]
    for x in xs do
      match carrierOf ctx (← inferType x) with
      | some c => cs := cs.push (str c)
      | none => return none
    return some (Json.mkObj [("set", Json.arr cs)])

def unsupported (what : String) (e : Expr) : M α := do
  throwError "unsupported {what}: {← ppExpr e}"

mutual

partial def term (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .fvar f := e then
    if let some n := lookup ctx.names f then return Json.mkObj [("v", str n)]
  let ty ← whnf (← inferType e)
  if ty.isForall then
    -- a predicate-valued argument: eta-expand over carriers
    return ← forallTelescope ty fun xs _ => do
      let mut vars : Array Json := #[]
      let mut ctx := ctx
      for x in xs do
        let some c := carrierOf ctx (← inferType x) | unsupported "lambda binder" e
        let v ← fresh ((← x.fvarId!.getDecl).userName)
        ctx := { ctx with names := ctx.names.push (x.fvarId!, v) }
        vars := vars.push (Json.mkObj [("v", str v), ("sort", str c)])
      let body ← formula ctx (mkAppN e xs).headBeta
      return Json.mkObj [("lam", Json.arr vars), ("body", body)]
  unsupported "term" e

partial def binder (ctx : Ctx) (q : String) (n : Name) (dom body : Expr) (bi : BinderInfo) : M Json := do
  let s? ← if dom.consumeMData.isProp then pure (some (str "Prop")) else sortOf ctx dom
  let some s := s? | unsupported "quantifier domain" dom
  if (s.getObjVal? "set").isOk then unsupported "quantifier over predicates" dom
  withLocalDecl n bi dom fun x => do
    let v ← fresh n
    let b ← formula { ctx with names := ctx.names.push (x.fvarId!, v) } (body.instantiate1 x)
    return Json.mkObj [("t", str q), ("v", str v), ("sort", s), ("body", b)]

partial def formula (ctx : Ctx) (e : Expr) : M Json := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  if let .forallE n dom body bi := e then
    if (← isProp dom) && !body.hasLooseBVars then
      return Json.mkObj [("t", str "imp"), ("a", ← formula ctx dom), ("b", ← formula ctx body)]
    return ← binder ctx "forall" n dom body bi
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let bin (t : String) := do
    return Json.mkObj [("t", str t), ("a", ← formula ctx args[0]!), ("b", ← formula ctx args[1]!)]
  match fn with
  | .const ``True _ => return Json.mkObj [("t", str "true")]
  | .const ``False _ => return Json.mkObj [("t", str "false")]
  | .const ``And _ => if args.size == 2 then return ← bin "and"
  | .const ``Or _ => if args.size == 2 then return ← bin "or"
  | .const ``Iff _ => if args.size == 2 then return ← bin "iff"
  | .const ``Not _ =>
    if args.size == 1 then return Json.mkObj [("t", str "not"), ("a", ← formula ctx args[0]!)]
  | .const ``Exists _ =>
    if args.size == 2 then
      match args[1]!.consumeMData with
      | .lam n dom body bi => return ← binder ctx "exists" n dom body bi
      | p =>
        let .forallE n dom _ bi ← whnf (← inferType p) | unsupported "existential" e
        return ← binder ctx "exists" n dom (mkApp (p.liftLooseBVars 0 1) (.bvar 0)) bi
  | .const ``Eq _ =>
    if args.size == 3 && (carrierOf ctx args[0]!).isSome then
      return Json.mkObj [("t", str "eq"), ("a", ← term ctx args[1]!), ("b", ← term ctx args[2]!)]
  | .const ``Ne _ =>
    if args.size == 3 && (carrierOf ctx args[0]!).isSome then
      return Json.mkObj [("t", str "not"), ("a", Json.mkObj [("t", str "eq"),
        ("a", ← term ctx args[1]!), ("b", ← term ctx args[2]!)])]
  | .fvar f =>
    if let some p := lookup ctx.names f then
      return Json.mkObj [("t", str "atom"), ("p", str p), ("args", Json.arr (← args.mapM (term ctx)))]
  | .const n _ =>
    if let some e' ← unfoldDefinition? e then
      unless (← get).unfolded.contains n do
        modify fun s => { s with unfolded := s.unfolded.push n }
      return ← formula ctx e'
  | _ => pure ()
  unsupported "formula" e

end

/-- Argument sorts of a predicate parameter `S₁ → … → Sₙ → Prop`. -/
def predicateArgs (ctx : Ctx) (ty : Expr) : MetaM (Option (Array Json)) :=
  forallTelescope ty fun ys body => do
    if ys.isEmpty || !body.consumeMData.isProp then return none
    let mut args : Array Json := #[]
    for y in ys do
      match ← sortOf ctx (← inferType y) with
      | some s => args := args.push s
      | none => return none
    return some args

def run (n : Name) : MetaM Json := do
  let some info := (← getEnv).find? n | throwError "unknown declaration {n}"
  forallTelescope info.type fun xs concl => do
    let mut ctx : Ctx := {}
    let mut carriers : Array Json := #[]
    let mut preds : Array Json := #[]
    let mut consts : Array Json := #[]
    let mut hyps : Array (String × Expr) := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let name := decl.userName.eraseMacroScopes.toString
      let ty ← instantiateMVars decl.type
      if ty.isProp then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr #[])])
      else if ty.isSort then
        ctx := { ctx with carriers := ctx.carriers.push (x.fvarId!, name) }
        carriers := carriers.push (str name)
      else if ← isProp ty then
        hyps := hyps.push (name, ty)
      else if let some c := carrierOf ctx ty then
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        consts := consts.push (Json.mkObj [("name", str name), ("sort", str c)])
      else
        let some args ← predicateArgs ctx ty
          | throwError "unsupported parameter {name} : {← ppExpr ty}"
        ctx := { ctx with names := ctx.names.push (x.fvarId!, name) }
        preds := preds.push (Json.mkObj [("name", str name), ("args", Json.arr args)])
    let pp (e : Expr) : MetaM String := do
      return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))
    let action : M Json := do
      let mut premises : Array Json := #[]
      for (name, ty) in hyps do
        let f ← formula ctx ty
        premises := premises.push (Json.mkObj [("name", str name), ("formula", f),
          ("lean", str (← pp ty))])
      let c ← formula ctx concl
      let st ← get
      return Json.mkObj [("theorem", str n.toString), ("carriers", Json.arr carriers),
        ("predicates", Json.arr preds), ("constants", Json.arr consts),
        ("premises", Json.arr premises),
        ("conclusion", Json.mkObj [("formula", c), ("lean", str (← pp concl))]),
        ("unfolded", Json.arr (st.unfolded.map (str ·.toString)))]
    action.run' {}

end Countermodel

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run scripts/Countermodel.lean input.json"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let thm ← IO.ofExcept (input.getObjValAs? String "theorem")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<countermodel>", fileMap := default, maxHeartbeats := 0 }
  let action : MetaM Json := do
    try Countermodel.run thm.toName
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  let (out, _) ← (MetaM.run' action).toIO ctx { env }
  IO.println out.compress
  return 0
