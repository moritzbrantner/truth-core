import TruthCore.Results.Modal.SelectedEffectBridge.Solution
import Mathlib.Order.Bounds.Basic

/-! Stipulative optimization constraints, not a sourced theory of perfect agency.
Candidate options need not exist at the world where a choice is made. Fixed
feasibility and quality are backgrounds, not consequences of necessary agency. -/
namespace TruthCore.Modal.OptimalCreationChoice
open TruthCore.Modal.SelectedEffectBridge
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.German.Kant.CosmologicalInference

/-- An admissible candidate achieves a greatest quality in the fixed image.
Distinct candidates can have the same quality; `IsGreatest` concerns values. -/
def Optimal {B V : Type} [PartialOrder V] (feasible : Set B) (quality : B → V)
    (x : B) : Prop := x ∈ feasible ∧ IsGreatest (quality '' feasible) (quality x)

/-- Every accessible performance has an output, and all its outputs are optimal.
This combines totality and optimality without asserting local functionality. -/
def OptimalOutputs {W B A V : Type} [PartialOrder V]
    (p : OutputProfile W B A) (w : W) (a : A)
    (feasible : Set B) (quality : B → V) : Prop :=
  ∀ v, (v = w ∨ p.ontic.frame.access w v) →
    (p.performs v a → ∃ x, p.output v a x) ∧ ∀ x, p.output v a x → Optimal feasible quality x

/-- All admissible candidates admit a strictly better admissible candidate. -/
def StrictlyImprovable {B V : Type} [PartialOrder V]
    (feasible : Set B) (quality : B → V) : Prop :=
  ∀ x ∈ feasible, ∃ y ∈ feasible, quality x < quality y

/-- Both alternating effect candidates are feasible, including the one absent
at the selected world. The source is not a creation candidate. -/
def tiedCandidates : Set EffectBeing := {x | ∃ b, x = some b}
def tiedQuality (_ : EffectBeing) : Nat := 0

/-- One general stability constraint, its causal consequence, the no-best
obstruction, and a tied-optimum control on the existing varying ontology. -/
def OptimalChoiceCertificate : Prop :=
  (∀ (W B A V : Type) [PartialOrder V] (p : OutputProfile W B A)
    (w : W) (a : A) (feasible : Set B) (quality : B → V),
    OptimalOutputs p w a feasible quality →
    (∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) →
    StableActOutput p w a) ∧
  (∀ (W B A V : Type) [PartialOrder V] (p : OutputProfile W B A)
    (w : W) (a : A) (x : B) (feasible : Set B) (quality : B → V),
    OptimalOutputs p w a feasible quality →
    (∀ x y, Optimal feasible quality x → Optimal feasible quality y → x = y) →
    SoundDistinctCauses p.ontic → RealizedOutputs p →
    SameActEverywhere p w a → p.output w a x →
    NecessaryAt p.ontic w x) ∧
  (∀ (B V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V),
    StrictlyImprovable feasible quality → ¬ ∃ x, Optimal feasible quality x) ∧
  (∀ (B V : Type) [PartialOrder V] (feasible : Set B) (quality : B → V) (x y : B),
    Optimal feasible quality x → Optimal feasible quality y → quality x = quality y) ∧
  StrictlyImprovable (Set.univ : Set Nat) id ∧
  (OptimalOutputs varying false () tiedCandidates tiedQuality ∧
    Optimal tiedCandidates tiedQuality firstEffect ∧
    Optimal tiedCandidates tiedQuality secondEffect ∧ firstEffect ≠ secondEffect ∧
    LocallyDeterministic varying ∧ ¬ StableActOutput varying false () ∧
    ContingentAt varying.ontic false firstEffect)
end TruthCore.Modal.OptimalCreationChoice
