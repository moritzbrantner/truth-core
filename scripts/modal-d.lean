import TruthCore.Modal.DResearch.Witnesses
import TruthCore.Modal.DResearch.Language

open TruthCore.Modal.DResearch
open TruthCore.Modal.ResearchFinite

def main : IO Unit := do
  IO.println "Pocket and fork:"
  IO.println TruthCore.Modal.DResearch.report
  IO.println "Fixed-language two-cycle:"
  IO.println (reprStr (cycle.worlds.map (fun w =>
    (w, cycle.worlds.map (fun v => (v, cycle.edge w v)),
      eval cycle w (.atom ()), eval cycle w (.box (.atom ())),
      eval cycle w (.diamond (.atom ())), witnesses cycle w (.atom ()),
      counterexamples cycle w (.atom ())))))
