/-
Advisory proof-term dependency export for registered Truth Core results (#959).

Run after a normal lake build, without rebuilding:
  lake env lean --run scripts/LeanReuse.lean <input.json>

Input: {"modules": ["TruthCore.X.Solution"], "theorems": ["TruthCore.X.theorem"],
        "inspect": ["TruthCore.X.theorem"]}.
For each inspected theorem, traverse constants syntactically referenced by its
elaborated proof term, following project-local theorem, definition and opaque
bodies. Only names in "theorems" are returned; imports and declaration types
are not evidence of proof use. This is reachability, not minimal logical need.
-/
import Lean

open Lean Meta

def describeProofUse (targets : Array String) (thm : Name) : MetaM Json := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? thm
    | return Json.mkObj [("theorem", Json.str thm.toString), ("error", Json.str "unknown theorem")]
  let mut pending := info.value.getUsedConstants
  let mut seen : NameSet := {}
  let mut referenced : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if n == thm || seen.contains n then continue
    seen := seen.insert n
    referenced := referenced.insert n
    -- Walk through local helpers; library definitions are boundaries.
    -- An axiom/constructor has no inspectable proof body.
    if !"TruthCore.".isPrefixOf n.toString then continue
    match env.find? n with
    | some (.thmInfo ci) => pending := pending ++ ci.value.getUsedConstants
    | some (.defnInfo ci) => pending := pending ++ ci.value.getUsedConstants
    | some (.opaqueInfo ci) => pending := pending ++ ci.value.getUsedConstants
    | _ => pure ()
  let used := (targets.filter fun t => referenced.contains t.toName).qsort (· < ·)
  return Json.mkObj [
    ("theorem", Json.str thm.toString),
    ("proof_theorems", toJson used)
  ]

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/LeanReuse.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let targets ← IO.ofExcept (input.getObjValAs? (Array String) "theorems")
  let inspect := (input.getObjValAs? (Array String) "inspect").toOption.getD targets
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<lean-reuse>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (MetaM.run' (inspect.mapM fun t => describeProofUse targets t.toName)).toIO ctx state
  IO.println (Json.arr out).compress
  return 0
