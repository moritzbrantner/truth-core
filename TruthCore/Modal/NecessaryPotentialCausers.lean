import TruthCore.Modal.ExistenceDegrees
import TruthCore.Models.NecessarilyUnderived

/-! A selected causal-union profile, not an identification of efficient
causation with grounding: the existing support-union parameter is explicitly
instantiated by Ontic.Causes. No intensity or degree-order premises are used.
The conclusion is negative non-distinctness; no equality-stability or excluded-middle inference to positive identity is
included. -/
namespace TruthCore.Modal.NecessaryPotentialCausers
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees

/-- Any two selected necessary pointwise universal other-directed potential
causers cannot be distinct. This neither supplies such a causer nor identifies
all necessary beings, and it does not assert positive equality constructively. -/
def NoDistinctNecessaryPotentialCausers {World Being : Type}
    (m : Ontic World Being) (w : World) : Prop :=
  ∀ a b, NecessaryAt m w a → OtherDirectedPotentialCause m w a →
    NecessaryAt m w b → OtherDirectedPotentialCause m w b → ¬ a ≠ b

/-- One unchanged registered interpretation jointly realizes distinct necessary
potential causers and worldwise well-founded support, but not union WF. The
same ordinary causal edges are explicitly selected as support edges here. -/
def RotatingControl : Prop :=
  let m := TruthCore.Models.NecessarilyUnderived.rotating
  ActualReflexive m false ∧
  NecessaryAt m false false ∧ NecessaryAt m false true ∧
  OtherDirectedPotentialCause m false false ∧
  OtherDirectedPotentialCause m false true ∧
  (∀ w, WellFoundedPresentEsseSupport m m.Causes w) ∧
  ¬ WellFoundedUnionNecessarySupport m m.Causes false ∧ false ≠ true
end TruthCore.Modal.NecessaryPotentialCausers
