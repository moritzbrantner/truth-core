import TruthCore.Modern.Hume.Regularity

/-! Selected competing commitments for #270, not whole historical worldviews.
The response-table rival is a causal account, not a reductive regularity theory.
Lewis's best-system identification is kept separate from that causal account. -/
namespace TruthCore.Comparison.HumeRegularity
open TruthCore.Modern.Hume.Regularity

def BareObservational (m : Experiment) : Prop := Conjunction m ∧ Nontrivial m

def InterventionEnriched (m : Experiment) : Prop :=
  Conjunction m ∧ Nontrivial m ∧ Changes m.setX ∧ ¬ Changes m.setY

def ScopedBrute (s : Scope) : Prop := LocalCausality s ∧ ¬ GroundedTotality s

end TruthCore.Comparison.HumeRegularity
