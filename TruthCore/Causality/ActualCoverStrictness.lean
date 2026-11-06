module

public import TruthCore.Causality.ActualCoverNecessaryBeing
public import TruthCore.Causality.CausalPowerConcreteness

/-!
A nonvacuous strictness witness for the existing actual-cover NE package (#418).
Three nonzero object roles form a V-shaped parthood order: shared is a proper
part of incomparable source and effect. This finite order specifies this model's
parthood, not a replacement for arbitrary orders or a universal fusion axiom.
At the actual world all three exist; only source exists at the other world.
The source causes both contingent objects. No cross-world downward existence
of parts is assumed. Causal/existential applicability remains OPEN; this is
neither a physical model nor a new NE derivation or constitutive-support cure.
-/

@[expose] public section
namespace TruthCore.Causality.ActualCoverStrictness
open BruteFoundationBoundary ActualFusionNecessaryBeing ActualCoverNecessaryBeing
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.WellFoundedSource
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

inductive Body | shared | source | effect deriving DecidableEq

instance : PartialOrder Body where
  le a b := a = b ∨ a = .shared
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with h | h
    · subst b; exact hbc
    · exact Or.inr h
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · exact h
    · rcases hba with h' | h'
      · exact h'.symm
      · exact h.trans h'.symm

/-- An actual causal contribution, with a non-abstract concrete source role.
Power will be assigned separately; no materiality or necessity is defined by it. -/
def causes (w : Bool) (c e : Body) : Prop :=
  c = .source ∧ e ≠ .source ∧ w = false

def profile : Profile Bool Body where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x = .source ∨ w = false
    Causes := causes }
  concrete := fun _ => True
  grounds := causes

/-- Explanation tokens are unused by the imported theorem. -/
def model : Model Bool Body where
  ontic := profile.ontic
  explains := fun _ _ _ => False

/-- One coherent package, including actual family/coverage/causal edges,
strict policy separation and application of the existing NE theorem. -/
def Certificate : Prop :=
  PopulatedAt model false ∧
  ConditionalActualCoverAt model.ontic false ∧
  ActualReflexive model.ontic false ∧
  ActualNoNecessaryPartsHaveCausesAt model.ontic false ∧
  CausesHaveActualEndpointsAt model.ontic false ∧
  CauseNotPartOfEffectAt model.ontic false ∧
  model.ontic.Causes false .source .effect ∧
  model.ontic.Causes false .source .shared ∧
  ActualNoNecessaryPartsFamily model.ontic false .effect ∧
  ActualNoNecessaryPartsFamily model.ontic false .shared ∧
  ActualCoverAt model.ontic false .effect ∧
  (.shared : Body) ≤ .source ∧ (.shared : Body) ≤ .effect ∧
  (.shared : Body) ≠ .source ∧ (.shared : Body) ≠ .effect ∧
  ¬ (.source : Body) ≤ .effect ∧ ¬ (.effect : Body) ≤ .source ∧
  Overlap (.source : Body) .effect ∧
  ¬ CauseEffectNonoverlapAt model.ontic false ∧
  (∃ p : CausalPowerConcreteness.IntendedProfile Bool Body,
    p.underlying = profile ∧
    (∀ x, ¬ p.abstract x) ∧
    (∀ w x, p.hasCausalPower w x ↔ x = .source)) ∧
  NecessaryBeing model.ontic false

end TruthCore.Causality.ActualCoverStrictness
