import TruthCore.Causality.EssentialPower
import TruthCore.German.Kant.CosmologicalInference

/-!
# How far inductive grounding goes toward the regress premise

`FINITE-GROUNDING-HAS-SOURCE` shows that inductively grounded power
(`FinitelyGroundedPower`) always reaches an intrinsic source by a finite path.
That is not yet the Second Way premise, which says every being is accessible
under the per se link (`NoInfinitePerSeEfficientCauseSeriesReading`). This
module states, as analyst's conditionals, exactly which further structure
closes the gap, and a countermodel showing that grounding alone does not.

It also states a conditional for Kant's local-causality countermodel: adding
well-foundedness of its `Causes` relation blocks the countermodel's pattern of
every existing being being contingent.

Nothing here is a source claim, and nothing here proves the regress premise or
any of the conditionals' antecedents of an actual causal relation. Kant's
`Causes` is a generic causal relation, not Aquinas's `CausesAsCaused`
(AGENTS.md invariant 6), so the Kant conditional uses Lean core's
`WellFounded` rather than the Aquinas reading.
-/

namespace TruthCore.Causality.GroundingRegress

open TruthCore.Causality
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.German.Kant.CosmologicalInference

/-- Intrinsic sources receive no per se link: nothing causes a source as a
caused cause. -/
def SourcesReceiveNoLink {Being : Type} (causesAsCaused : Being → Being → Prop)
    (intrinsic : Being → Prop) : Prop :=
  ∀ x, intrinsic x → ∀ y, ¬ causesAsCaused y x

/-- Each being has at most one immediate per se cause: the per se series
through any being is linear, as in the stone–stick–hand example. -/
def AtMostOneImmediateCause {Being : Type}
    (causesAsCaused : Being → Being → Prop) : Prop :=
  ∀ x y z, causesAsCaused y x → causesAsCaused z x → y = z

/-- For every relation and source predicate: if every being's power is
inductively grounded, sources receive no per se link, and each being has at
most one immediate per se cause, then every being is accessible under the per
se link (the corpus's reading of the regress premise). -/
def GroundingWithUniqueCauseYieldsRegressReading : Prop :=
  ∀ (Being : Type) (causesAsCaused : Being → Being → Prop)
    (intrinsic : Being → Prop),
    (∀ x, FinitelyGroundedPower causesAsCaused intrinsic x) →
      SourcesReceiveNoLink causesAsCaused intrinsic →
        AtMostOneImmediateCause causesAsCaused →
          NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused

/-- The uniqueness condition is not idle: there is a relation and a source
predicate on which every being's power is inductively grounded and the source
receives no link, yet not every being is accessible, because an infinite
descending chain runs alongside the grounding links. -/
def GroundingWithoutUniqueCauseAllowsRegress : Prop :=
  ∃ (causesAsCaused : Option Nat → Option Nat → Prop)
    (intrinsic : Option Nat → Prop),
    (∀ x, FinitelyGroundedPower causesAsCaused intrinsic x) ∧
      SourcesReceiveNoLink causesAsCaused intrinsic ∧
        ¬ NoInfinitePerSeEfficientCauseSeriesReading causesAsCaused

/-- For every Kantian ontic model and world: if the local causal principle
holds and the world's causal relation is well-founded, then, provided something
exists at that world, not every existing being there is contingent. This is the
pattern `LocalCausalityInsufficient` exhibits without well-foundedness. The
conclusion is the negation of a universal; it does not name a non-contingent
being, and it does not assert a necessary being. -/
def WellFoundedCausesBlockAllContingent : Prop :=
  ∀ (World Entity : Type) (m : Ontic World Entity) (w : World),
    LocalCausalPrinciple m → WellFounded (m.Causes w) →
      (∃ x, m.ExistsAt w x) →
        ¬ ∀ x, m.ExistsAt w x → ContingentAt m w x

end TruthCore.Causality.GroundingRegress
