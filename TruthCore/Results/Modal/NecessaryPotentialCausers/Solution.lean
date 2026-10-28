import Mathlib.Order.RelClasses
import TruthCore.Modal.NecessaryPotentialCausers
namespace TruthCore.Results.Modal.NecessaryPotentialCausers
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Modal.NecessaryPotentialCausers
/-- A selected causal-support profile: R is explicitly m.Causes, not an
identification of generic efficient causation with metaphysical grounding. -/
theorem noDistinct {World Being : Type} (m : Ontic World Being) (w : World)
    (a b : Being) (hRef : ActualReflexive m w)
    (ha : NecessaryAt m w a) (hb : NecessaryAt m w b)
    (hpa : OtherDirectedPotentialCause m w a)
    (hpb : OtherDirectedPotentialCause m w b)
    (hWF : WellFoundedUnionNecessarySupport m m.Causes w) : ¬ a ≠ b := by
  intro hab
  have hba : b ≠ a := fun h => hab h.symm
  obtain ⟨u, hu, hEdgeAB⟩ := hpa w hRef b (hb w hRef) hba
  obtain ⟨v, hv, hEdgeBA⟩ := hpb w hRef a (ha w hRef) hab
  have eAB : UnionNecessarySupport m m.Causes w a b :=
    ⟨ha, hb, u, ha u hu, hEdgeAB⟩
  have eBA : UnionNecessarySupport m m.Causes w b a :=
    ⟨hb, ha, v, hb v hv, hEdgeBA⟩
  exact @WellFounded.asymmetric _ _ hWF a b eAB eBA


/-- A transparent role-quantified constraint avoids duplicated premise IDs.
The support parameter is explicitly the model's ordinary causal relation. -/
theorem checks {World Being : Type} (m : Ontic World Being) (w : World)
    (hRef : ActualReflexive m w)
    (hWF : WellFoundedUnionNecessarySupport m m.Causes w) :
    NoDistinctNecessaryPotentialCausers m w := by
  intro a b ha hpa hb hpb
  exact noDistinct m w a b hRef ha hb hpa hpb hWF
end TruthCore.Results.Modal.NecessaryPotentialCausers
