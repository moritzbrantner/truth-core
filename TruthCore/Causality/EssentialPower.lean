import TruthCore.Causality.LocalTransmission

namespace TruthCore.Causality
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A *local transmission rule*: a node is active exactly when an immediate
cause linked to it is active. This captures current instrumental dependence,
including a response to cutting an edge, but does not choose a least or
greatest solution or establish metaphysical grounding. -/
def PowerTransmissionRule {Being : Type}
    (causesAsCaused : Being → Being → Prop) (active : Being → Prop) : Prop :=
  ∀ x, active x ↔ ∃ y, causesAsCaused y x ∧ active y

/-- An infinite successor chain admits both on and off solutions to the
transmission equations. Even if cutting any one edge can extinguish every
downstream node while preserving upstream activity, these equations do not
determine whether the intact chain acts. -/
def EssentialPowerUnderdetermined : Prop :=
  ∃ (causesAsCaused : Nat → Nat → Prop) (on off : Nat → Prop),
    (∀ n, causesAsCaused (n + 1) n) ∧
    PowerTransmissionRule causesAsCaused on ∧
    PowerTransmissionRule causesAsCaused off ∧
    on 0 ∧ ¬ off 0 ∧
    (∀ cut, ∃ afterCut : Nat → Prop,
      PowerTransmissionRule
        (fun y x => causesAsCaused y x ∧ x ≠ cut) afterCut ∧
      (∀ n, n ≤ cut → ¬ afterCut n) ∧
      (∀ n, cut < n → afterCut n)) ∧
    ¬ NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused

/-- A finite path through the upstream cause relation, including the zero-
length path. Its finiteness is explicit in the inductive constructors. -/
inductive FiniteCausalPath {Being : Type}
    (causesAsCaused : Being → Being → Prop) : Being → Being → Prop where
  | same (x) : FiniteCausalPath causesAsCaused x x
  | link {x y z} : causesAsCaused y x →
      FiniteCausalPath causesAsCaused y z → FiniteCausalPath causesAsCaused x z

/-- Power grounded in an independent source by a finite number of actually
transmitting links. The choice that metaphysical causal power must have
*this* inductive structure is left open: it is not a theorem of local
transmission or of an infinite relation alone. -/
inductive FinitelyGroundedPower {Being : Type}
    (causesAsCaused : Being → Being → Prop)
    (intrinsic : Being → Prop) : Being → Prop where
  | intrinsic (x) : intrinsic x →
      FinitelyGroundedPower causesAsCaused intrinsic x
  | borrowed {x y} : causesAsCaused y x →
      FinitelyGroundedPower causesAsCaused intrinsic y →
      FinitelyGroundedPower causesAsCaused intrinsic x

/-- This grounding semantics always yields an actual source and a finite
dependency path to it; the theorem does not equate `FinitelyGroundedPower`
with every possible metaphysical account of *per se* causal power. -/
def FiniteGroundingHasSource : Prop :=
  ∀ (Being : Type) (causesAsCaused : Being → Being → Prop)
    (intrinsic : Being → Prop) (x : Being),
    FinitelyGroundedPower causesAsCaused intrinsic x →
      ∃ source, FiniteCausalPath causesAsCaused x source ∧ intrinsic source

end TruthCore.Causality
