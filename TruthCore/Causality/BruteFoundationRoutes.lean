import TruthCore.Causality.BruteFoundationBoundary

/-!
# Three routes beyond a contingent brute foundation (#505)

Analyst-defined discriminating controls, not attributed primary-source claims.
Reuse the modal and causal definitions and rigid identity policy in #510.

Modal contingency does not by itself entail an intrinsic passive potency.
A token satisfying weak explanation coverage need not provide a sufficient,
concrete, noncircular reason. Necessary source + strict effect necessitation
excludes contingent effect. Each disputed bridge remains open.
-/

namespace TruthCore.Causality.BruteFoundationRoutes

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference

/-- Only a child has the stipulated passive potency. Not defined as contingency. -/
def PassivePotencyAt (_w : Bool) (x : Bool × Bool) : Prop := x.2 = true

/-- Every existing bearer of this modeled potency has an existing actualizer. -/
theorem everyModeledPassivePotencyActualized :
    ∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x → PassivePotencyAt w x →
      ∃ y, boundaryRival.concrete y ∧ boundaryRival.ontic.ExistsAt w y ∧
        boundaryRival.grounds w y x := by
  exact boundaryRivalNoninitialGrounded

/-- A concrete actual contingent root need not have this passive potency. -/
theorem contingentRootWithoutPassivePotency :
    boundaryRival.concrete (false, false) ∧
    boundaryRival.ontic.ExistsAt false (false, false) ∧
    ContingentAt boundaryRival.ontic false (false, false) ∧
    ¬ PassivePotencyAt false (false, false) := by
  refine ⟨True.intro, rfl,
    boundaryRivalAllContingent false (false, false) rfl, ?_⟩
  intro h
  cases h

/-- The actualization rule does not imply necessary concrete existence. -/
theorem potencyActualizationDoesNotExcludeBruteRoot :
    (∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x → PassivePotencyAt w x →
      ∃ y, boundaryRival.concrete y ∧ boundaryRival.ontic.ExistsAt w y ∧
        boundaryRival.grounds w y x) ∧
    ¬ NecessaryConcreteAt boundaryRival false ∧
    ¬ EveryContingentGroundedAt boundaryRival false := by
  exact ⟨everyModeledPassivePotencyActualized,
    boundaryRivalNoNecessary, boundaryRivalHasBruteRoot⟩

/-- Add explicitly the philosophically disputed contingency-to-potency bridge.
The resulting necessity theorem imports #510 rather than reproving it. -/
theorem necessaryConcreteFromPotencyBridge
    (m : Profile W B) (w : W) (passive : B → Prop)
    (hPop : InhabitedAt m w)
    (hWF : WellFounded (m.grounds w))
    (hContingentPassive :
      ∀ x, m.concrete x → m.ontic.ExistsAt w x →
        ContingentAt m.ontic w x → passive x)
    (hActualization :
      ∀ x, m.concrete x → m.ontic.ExistsAt w x →
        passive x →
        ∃ y, m.concrete y ∧ m.ontic.ExistsAt w y ∧ m.grounds w y x) :
    NecessaryConcreteAt m w := by
  apply necessaryConcreteOfGroundedContingents m w hPop hWF
  intro x hc he hContingent
  exact hActualization x hc he
    (hContingentPassive x hc he hContingent)

/-- Weak reason witness: the complete-world selection token accompanies
the actual existence of an entity. No concrete bearer, noncircularity, or
independent explanatory adequacy is established by this interpretation. -/
def SelectionReason (w token : Bool) (x : Bool × Bool) : Prop :=
  token = w ∧ boundaryRival.ontic.ExistsAt w x

theorem everyActualHasSelectionReason :
    ∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x →
      ∃ token : Bool, SelectionReason w token x := by
  intro w x _ hex
  exact ⟨w, rfl, hex⟩

theorem selectionReasonsAttachToExisting :
    ∀ w token x, SelectionReason w token x →
      boundaryRival.ontic.ExistsAt w x := by
  intro w token x h
  exact h.2

/-- Weak explanation coverage and truth soundness leave the brute root intact.
This is a countermodel to an inference from a bare explanation relation,
not a model of independently sufficient philosophical explanation. -/
theorem weakExplanationsDoNotExcludeBruteRoot :
    (∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x →
      ∃ token : Bool, SelectionReason w token x) ∧
    (∀ w token x, SelectionReason w token x →
      boundaryRival.ontic.ExistsAt w x) ∧
    ¬ EveryContingentGroundedAt boundaryRival false ∧
    ¬ NecessaryConcreteAt boundaryRival false := by
  exact ⟨everyActualHasSelectionReason,
    selectionReasonsAttachToExisting,
    boundaryRivalHasBruteRoot, boundaryRivalNoNecessary⟩

/-- Necessity of a source plus an invariant, strictly necessitating existence
rule entails necessity of its particular effect. Such strict sufficiency is
not supplied merely by the semantics of grounding or efficient causation. -/
theorem necessarySourceAndNecessitatingRule
    (m : Ontic W B) (w : W) (source effect : B)
    (hNecessary : NecessaryAt m w source)
    (hNecessitates : ∀ v, m.frame.access w v →
      m.ExistsAt v source → m.ExistsAt v effect) :
    NecessaryAt m w effect := by
  intro v hv
  exact hNecessitates v hv (hNecessary v hv)

/-- A contingent effect refutes joint necessary source + strict necessary
effect sufficiency. A nonnecessitating selection or contingent act survives. -/
theorem noContingentEffectFromNecessaryStrictSufficiency
    (m : Ontic W B) (w : W) (source effect : B)
    (hNecessary : NecessaryAt m w source)
    (hNecessitates : ∀ v, m.frame.access w v →
      m.ExistsAt v source → m.ExistsAt v effect)
    (hAbsent : ∃ v, m.frame.access w v ∧ ¬ m.ExistsAt v effect) :
    False := by
  rcases hAbsent with ⟨v, hv, hNot⟩
  exact hNot ((necessarySourceAndNecessitatingRule m w source effect
    hNecessary hNecessitates) v hv)

/-- The two weak routes survive jointly with well-founded grounding and
a nonempty concrete inventory in every world. -/
theorem combinedWeakRoutesSurvive :
    (∀ w, InhabitedAt boundaryRival w) ∧
    (∀ w, WellFounded (boundaryRival.grounds w)) ∧
    (∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x → PassivePotencyAt w x →
      ∃ y, boundaryRival.concrete y ∧ boundaryRival.ontic.ExistsAt w y ∧
        boundaryRival.grounds w y x) ∧
    (∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x →
      ∃ token : Bool, SelectionReason w token x) ∧
    ¬ NecessaryConcreteAt boundaryRival false := by
  exact ⟨boundaryRivalInhabited, boundaryRivalWellFounded,
    everyModeledPassivePotencyActualized,
    everyActualHasSelectionReason,
    boundaryRivalNoNecessary⟩

end TruthCore.Causality.BruteFoundationRoutes
