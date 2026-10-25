import TruthCore.Modal.KResearch

def main : IO Unit := do
  IO.println "fork (branch is a sink):"
  IO.println (TruthCore.Modal.KResearch.report false)
  IO.println "chain-fork (branch accesses sink):"
  IO.println (TruthCore.Modal.KResearch.report true)
