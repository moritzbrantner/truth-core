import Lean
import TruthCore.Logic.StrengthComparison

/-!
Bind selected comparison certificates to their entire elaborated types. This is
semantic binding, not a replacement for Lean/Comparator/NanoDa verification.
The specification fixes ordered vocabulary parameters and background premises.
Only supplied certificates are inspected; the environment is never searched for
proofs of either proposition.
-/
open Lean Meta
open TruthCore.Logic.StrengthComparison

namespace CheckStrength

def str := Json.str
def pp (e : Expr) : MetaM String := return toString (← ppExpr e)
def ppExplicit (e : Expr) : MetaM String :=
  withOptions (fun opts => (opts.setBool `pp.explicit true).setBool `pp.universes true) (pp e)

def object (j : Json) (key : String) : MetaM Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throwError "{e}"

def string (j : Json) (key : String) : MetaM String :=
  match j.getObjValAs? String key with
  | .ok v => pure v
  | .error e => throwError "{e}"

def project (s : Expr) (field : Name) : MetaM Expr := do
  -- Only reduce the projection/specification, retaining the proposition's own
  -- named declaration and its full ordered arguments.
  let body ← whnf s
  if !body.isAppOfArity ``ComparisonSpec.mk 5 then
    throwError "specification must reduce to ComparisonSpec constructor"
  let index := if field == ``ComparisonSpec.background then 0
    else if field == ``ComparisonSpec.stronger then 1
    else if field == ``ComparisonSpec.weaker then 2
    else if field == ``ComparisonSpec.delta then 3 else 4
  return body.getAppArgs[index]!

def roleName (role : String) : Option Name :=
  match role with
  | "implication" => some ``Implication
  | "delta_forward" => some ``DeltaForward
  | "reconstruction" => some ``Reconstruction
  | "equivalence" => some ``TruthCore.Logic.StrengthComparison.Equivalence
  | "converse" => some ``Converse
  | "allowed_cases" => some ``AllowedCases
  | "remainder_identity" => some ``RemainderIdentity
  | _ => none

partial def underBackground (list : Expr) (body : Expr) : MetaM Expr := do
  let list ← whnf list
  if list.isAppOf ``List.nil then return body
  if list.isAppOfArity ``List.cons 3 then
    return ← mkArrow list.appFn!.appArg! (← underBackground list.appArg! body)
  throwError "background must be a finite list"

def expectedBody (spec : Expr) (role : String) : MetaM Expr := do
  let s ← project spec ``ComparisonSpec.stronger
  let w ← project spec ``ComparisonSpec.weaker
  let d ← project spec ``ComparisonSpec.delta
  let r ← project spec ``ComparisonSpec.remainder
  let body ← match role with
    | "implication" => mkArrow s w
    | "delta_forward" => mkArrow s d
    | "reconstruction" => mkArrow w (← mkArrow d s)
    | "equivalence" => mkAppM ``Iff #[s, ← mkAppM ``And #[w, d]]
    | "converse" => mkArrow w s
    | "allowed_cases" => mkAppM ``Iff #[w, ← mkAppM ``Or #[s, r]]
    | "remainder_identity" => mkAppM ``Iff #[r, ← mkAppM ``And #[w, ← mkAppM ``Not #[s]]]
    | _ => throwError "unknown certificate role {role}"
  -- Helpers are constructed as expressions so the readable expected type shows
  -- the actual applications instead of a wrapper naming the obligation.
  underBackground (← project spec ``ComparisonSpec.background) body

def certificate (xs : Array Expr) (spec : Expr) (request : Json) : MetaM Json := do
  let role ← string request "role"
  let thmName ← string request "theorem"
  let some _ := roleName role | throwError "unknown certificate role {role}"
  let expected ← mkForallFVars xs (← expectedBody spec role)
  let theoremConstant ← mkConstWithFreshMVarLevels thmName.toName
  let actual ← inferType theoremConstant
  let agrees ← isDefEq actual expected
  return Json.mkObj [("role", str role), ("theorem", str thmName),
    ("theorem_application", str (← ppExplicit (← instantiateMVars (mkAppN theoremConstant xs)))),
    ("expected_type", str (← pp expected)), ("actual_type", str (← pp actual)),
    ("axioms", toJson ((← collectAxioms thmName.toName).map Name.toString)),
    ("bound", Json.bool agrees)]

def head? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => some n
  | _ => none

def fieldBinding (role : String) (e : Expr) (declaration : String) : MetaM Json := do
  return Json.mkObj [("role", str role), ("declaration", str declaration),
    ("expression", str (← pp e)), ("explicit_application", str (← ppExplicit e)), ("type", str (← pp (← inferType e))),
    ("bound", Json.bool ((head? e).map Name.toString == some declaration))]

partial def propositionList (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return #[]
  if e.isAppOfArity ``List.cons 3 then
    return #[e.appFn!.appArg!] ++ (← propositionList e.appArg!)
  throwError "background must reduce to a finite list of propositions"

def separation (specName : Name) (request : Json) : MetaM Json := do
  let setting ← string request "setting"
  let thmName ← string request "theorem"
  let some (.defnInfo info) := (← getEnv).find? setting.toName
    | throwError "separator setting must be a definition"
  if !info.levelParams.isEmpty then throwError "separator setting must have no universe parameters"
  if !(← isDefEq info.type (mkConst ``ComparisonSpec)) then
    throwError "separator setting must be a closed ComparisonSpec"
  let application := info.value.consumeMData
  if head? application != some specName then
    throwError "separator setting must directly apply the selected specification"
  let _ ← inferType application
  let expected ← mkAppM ``Separation #[application]
  let actual ← inferType (← mkConstWithFreshMVarLevels thmName.toName)
  let agrees ← isDefEq actual expected
  let mut parameters : Array Json := #[]
  for arg in application.getAppArgs do
    parameters := parameters.push (Json.mkObj [("expression", str (← pp arg)), ("type", str (← pp (← inferType arg)))])
  return Json.mkObj [("setting", str setting), ("theorem", str thmName),
    ("application", str (← pp application)), ("explicit_application", str (← ppExplicit application)), ("parameters", Json.arr parameters),
    ("expected_type", str (← pp expected)), ("actual_type", str (← pp actual)),
    ("axioms", toJson ((← collectAxioms thmName.toName).map Name.toString)), ("bound", Json.bool agrees)]

def describe (request : Json) : MetaM Json := do
  let id ← string request "id"
  let specification ← string request "specification"
  let some specInfo := (← getEnv).find? specification.toName
    | throwError "unknown comparison specification {specification}"
  -- Specification universes are fixed parameters, not unification variables:
  -- a monomorphic certificate must not specialize a polymorphic comparison.
  let constant := mkConst specification.toName (specInfo.levelParams.map mkLevelParam)
  let specType ← inferType constant
  forallTelescope specType fun xs result => do
    if !(← isDefEq result (mkConst ``ComparisonSpec)) then
      throwError "specification must return ComparisonSpec"
    let spec := mkAppN constant xs
    let strong ← project spec ``ComparisonSpec.stronger
    let weak ← project spec ``ComparisonSpec.weaker
    let delta ← project spec ``ComparisonSpec.delta
    let remainder ← project spec ``ComparisonSpec.remainder
    let background ← propositionList (← project spec ``ComparisonSpec.background)
    let mut parameters : Array Json := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if ← isProp decl.type then
        throwError "proof-valued specification parameter {decl.userName} hides a background assumption; put it in background"
      parameters := parameters.push (Json.mkObj [("name", str decl.userName.toString),
        ("type", str (← pp decl.type)), ("binder_info", str (reprStr decl.binderInfo))])
    let cs ← object request "certificates"
    let cs ← match cs.getArr? with | .ok a => pure a | .error e => throwError "{e}"
    let certificates ← cs.mapM (certificate xs spec)
    let mut bindings : Array Json := #[]
    if let .ok ds := request.getObjVal? "statement_declarations" then
      for (role, e) in [("stronger", strong), ("weaker", weak), ("delta", delta), ("remainder", remainder)] do
        if let .ok name := ds.getObjValAs? String role then
          bindings := bindings.push (← fieldBinding role e name)
      if let .ok bgs := ds.getObjValAs? (Array String) "background" then
        if bgs.size != background.size then throwError "background statement count differs from specification"
        for i in [:bgs.size] do
          bindings := bindings.push (← fieldBinding ("background." ++ toString i) background[i]! bgs[i]!)
    let mut out := [("id", str id), ("specification", str specification),
      ("application", str (← pp spec)), ("parameters", Json.arr parameters),
      ("explicit_application", str (← ppExplicit spec)), ("universe_parameters", toJson (specInfo.levelParams.map Name.toString)),
      ("formulas", Json.mkObj [("background", toJson (← background.mapM pp)),
        ("stronger", str (← pp strong)), ("weaker", str (← pp weak)),
        ("delta", str (← pp delta)), ("remainder", str (← pp remainder))]),
      ("field_bindings", Json.arr bindings), ("certificates", Json.arr certificates)]
    let dSame ← isDefEq delta strong
    let dImp ← isDefEq delta (← mkArrow weak strong)
    out := out ++ [("delta_degenerate", Json.bool (dSame || dImp))]
    let mut allAgree := certificates.all fun c => (c.getObjValAs? Bool "bound").toOption.getD false
    allAgree := allAgree && bindings.all fun b => (b.getObjValAs? Bool "bound").toOption.getD false
    if let .ok separator := request.getObjVal? "separator" then
      let sep ← separation specification.toName separator
      allAgree := allAgree && (sep.getObjValAs? Bool "bound").toOption.getD false
      out := out ++ [("separator", sep)]
    return Json.mkObj (out ++ [("bound", Json.bool allAgree)])

end CheckStrength

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run scripts/CheckStrength.lean input.json"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let comparisons ← IO.ofExcept (input.getObjValAs? (Array Json) "comparisons")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<check-strength>", fileMap := default, maxHeartbeats := 0 }
  let (out, _) ← (MetaM.run' (comparisons.mapM fun request => do
    try CheckStrength.describe request
    catch e => return Json.mkObj [("id", (request.getObjVal? "id").toOption.getD Json.null),
      ("bound", Json.bool false), ("error", Json.str (← e.toMessageData.toString))])).toIO ctx { env }
  IO.println (Json.arr out).compress
  return 0
