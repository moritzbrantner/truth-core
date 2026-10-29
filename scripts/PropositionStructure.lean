import Lean
/-!
Derived structural presentation of elaborated expressions with visible depth limits. No proof status
or independent atom semantics is assigned here. Requested project definitions
are exposed by their stored bodies, without delta/Boolean normalization.
Input: {modules: [String], declarations: [String], unfold?: [String]}.
-/
open Lean Meta

namespace PropositionStructure

def str (s : String) : Json := Json.str s

def edge (role : String) (node : Json) : Json :=
  Json.mkObj [("role", str role), ("node", node)]

def project (n : Name) : Bool := n.toString.startsWith "TruthCore."

def definable (n : Name) : MetaM Bool := do
  return project n && !(← getEnv).isProjectionFn n && match (← getEnv).find? n with
    | some (.defnInfo _) => true
    | _ => false

/-- Binding identifiers are tree addresses, independent of transient Lean FVarIds. -/
abbrev Bindings := List (FVarId × String)

partial def tree (e : Expr) (path : String) (bindings : Bindings) (fuel : Nat := 100) : MetaM Json := do
  let text ← ppExpr e
  let ty ← try pure (toString (← ppExpr (← inferType e))) catch _ => pure "<type unavailable>"
  let base := [("id", str path), ("text", str (toString text)), ("type", str ty)]
  if fuel == 0 then
    return Json.mkObj (base ++ [("kind", str "unsupported"), ("coverage", str "partial: depth limit"), ("children", Json.arr #[])])
  let child (role : String) (e : Expr) := do
    return edge role (← tree e (path ++ "/" ++ role) bindings (fuel - 1))
  let mut kind := "unsupported"
  let mut coverage := if ty == "<type unavailable>" then "partial: type inference unavailable" else "complete"
  let mut children : Array Json := #[]
  let mut extra : List (String × Json) := []
  match e with
  | .const n levels =>
    kind := "constant"
    let available ← definable n
    let env ← getEnv
    extra := [("declaration", str n.toString), ("universes", toJson (levels.map toString)),
      ("unfold_available", Json.bool available),
      ("boundary", str (if available then "project definition" else if env.isProjectionFn n then "primitive structure field" else if project n then "project named boundary" else "library boundary"))]
  | .fvar f =>
    kind := "variable"
    if let some (_, address) := bindings.find? (·.1 == f) then
      extra := [("binding", str address)]
    else
      coverage := "partial: free variable outside extracted scope"
  | .bvar i =>
    kind := "unsupported"
    coverage := "partial: loose bound variable"
    extra := [("index", toJson i)]
  | .mvar m =>
    coverage := "partial: unresolved metavariable"
    extra := [("metavariable", str m.name.toString)]
  | .sort u => kind := "sort"; extra := [("universe", str (toString u))]
  | .lit l => kind := "literal"; extra := [("literal", str (reprStr l))]
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    kind := if fn.isConstOf ``And && args.size == 2 then "and"
      else if fn.isConstOf ``Or && args.size == 2 then "or"
      else if fn.isConstOf ``Not && args.size == 1 then "not"
      else if fn.isConstOf ``Iff && args.size == 2 then "iff"
      else if fn.isConstOf ``Exists && args.size == 2 then "exists"
      else "application"
    children := children.push (← child "function" fn)
    for i in [:args.size] do
      children := children.push (← child ("argument." ++ toString i) args[i]!)
  | .lam n dom body bi | .forallE n dom body bi =>
    let isLam := match e with | .lam .. => true | _ => false
    let domProp ← isProp dom
    kind := if isLam then "lambda" else if !body.hasLooseBVar 0 && domProp then "implication" else "forall"
    extra := [("binder_name", str n.toString), ("binder_info", str (reprStr bi))]
    children := children.push (← child "domain" dom)
    let b ← withLocalDecl n bi dom fun x =>
      tree (body.instantiate1 x) (path ++ "/body") ((x.fvarId!, path) :: bindings) (fuel - 1)
    children := children.push (edge "body" b)
  | .letE n dom value body _ =>
    kind := "let"
    extra := [("binder_name", str n.toString)]
    children := children.push (← child "domain" dom)
    children := children.push (← child "value" value)
    let b ← withLetDecl n dom value fun x =>
      tree (body.instantiate1 x) (path ++ "/body") ((x.fvarId!, path) :: bindings) (fuel - 1)
    children := children.push (edge "body" b)
  | .proj n i value =>
    kind := "projection"
    extra := [("declaration", str n.toString), ("field_index", toJson i), ("boundary", str "structure field")]
    children := children.push (← child "structure" value)
  | .mdata _ body =>
    kind := "metadata"
    children := children.push (← child "expression" body)
  return Json.mkObj (base ++ [("kind", str kind), ("coverage", str coverage), ("children", Json.arr children)] ++ extra)

partial def constants (e : Expr) : Array Name :=
  match e with
  | .const n _ => #[n]
  | .app f a => constants f ++ constants a
  | .lam _ d b _ | .forallE _ d b _ => constants d ++ constants b
  | .letE _ d v b _ => constants d ++ constants v ++ constants b
  | .mdata _ b => constants b
  | .proj n _ b => #[n] ++ constants b
  | _ => #[]

def reference (n : Name) : MetaM Json := do
  let some info := (← getEnv).find? n
    | return Json.mkObj [("declaration", str n.toString), ("kind", str "unresolved")]
  let mut fields : Array Json := #[]
  if let some s := getStructureInfo? (← getEnv) n then
    for field in s.fieldInfo do
      let f := field.projFn
      if let some fi := (← getEnv).find? f then
        fields := fields.push (Json.mkObj [("declaration", str f.toString), ("type", str (toString (← ppExpr fi.type))), ("is_law", Json.bool (← isProp fi.type))])
  let available ← definable n
  return Json.mkObj [("declaration", str n.toString), ("type", str (toString (← ppExpr info.type))),
    ("kind", str (if !fields.isEmpty then "structure" else if available then "definition" else "named boundary")),
    ("is_class", Json.bool (isClass (← getEnv) n)), ("fields", Json.arr fields)]

def describe (unfold : Array String) (maxDepth : Nat) (n : Name) : MetaM Json := do
  let some info := (← getEnv).find? n
    | return Json.mkObj [("declaration", str n.toString), ("error", str "unknown declaration")]
  let mut fields := [("declaration", str n.toString), ("type", ← tree info.type (n.toString ++ "/type") [] maxDepth)]
  let mut refs := constants info.type
  if unfold.contains n.toString then
    if ← definable n then
      if let .defnInfo d := info then
        fields := fields ++ [("expansion", ← tree d.value (n.toString ++ "/expansion") [] maxDepth)]
        refs := refs ++ constants d.value
      else
        fields := fields ++ [("unfold_status", str "named boundary: not a project definition")]
    else
      fields := fields ++ [("unfold_status", str (if project n then "primitive or named project boundary retained" else "library boundary retained"))]
  let mut seen : Array Name := #[]
  let mut references : Array Json := #[]
  let env ← getEnv
  let direct := refs
  for ref in direct do
    if let some ri := (← getEnv).find? ref then
      refs := refs ++ (constants ri.type).filter (fun r => (getStructureInfo? env r).isSome)
  for ref in refs do
    if seen.contains ref then continue
    seen := seen.push ref
    references := references.push (← reference ref)
  return Json.mkObj (fields ++ [("references", Json.arr references), ("coverage", str "structural; named boundaries retained; no semantic or proof inference")])

end PropositionStructure

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: lean --run scripts/PropositionStructure.lean input.json"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let declarations ← IO.ofExcept (input.getObjValAs? (Array String) "declarations")
  let unfold := (input.getObjValAs? (Array String) "unfold").toOption.getD #[]
  let maxDepth := min 200 ((input.getObjValAs? Nat "max_depth").toOption.getD 100)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<proposition-structure>", fileMap := default, maxHeartbeats := 0 }
  let (out, _) ← (MetaM.run' (declarations.mapM fun d => PropositionStructure.describe unfold maxDepth d.toName)).toIO ctx { env }
  IO.println (Json.arr out).compress
  return 0
