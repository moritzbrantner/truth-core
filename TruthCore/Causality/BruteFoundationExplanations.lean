import TruthCore.Causality.BruteFoundationBoundary

/-!
# Explanatory coverage is weaker than necessitating explanation

These are analyst-constructed controls for #505, #485, and #312. The shared
profile and its two-world contingent roots come from BruteFoundationBoundary.
A reason token is NOT an ontic individual. In particular, its presence does
not make it a concrete bearer with powers or an efficient cause.

A world-relative 'explains' relation is deliberately weak: assigning a true
reason to an actual fact neither proves complete explanation nor entails that
the explanandum is true wherever the reason is present. The difference is
tested below, not passed off as an argument for a necessary being.
-/

namespace TruthCore.Causality.BruteFoundationExplanations

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference

/-- An explanation token is not by definition an existent concrete cause.
Truth of a reason-token at a world, existence of the subject at the world, and
the explanatory relation are independently specified. -/
structure ExplanationProfile (World Being Reason : Type) where
  reality : Profile World Being
  reasonPresent : World → Reason → Prop
  explains : World → Reason → Being → Prop

/-- Every actually existing concrete individual has some true explanation
token. Unlike the strong causal bridge, this does not demand a concrete cause. -/
def LocallyExplained (m : ExplanationProfile W B R) : Prop :=
  ∀ w x, m.reality.concrete x → m.reality.ontic.ExistsAt w x →
    ∃ reason, m.reasonPresent w reason ∧ m.explains w reason x

/-- An actual-world explanatory link only refers to a reason true there and
an actual concrete being. This says nothing about its modal sufficiency. -/
def ExplanationSound (m : ExplanationProfile W B R) : Prop :=
  ∀ w r x, m.explains w r x →
    m.reasonPresent w r ∧ m.reality.concrete x ∧
      m.reality.ontic.ExistsAt w x

/-- The reason is present in every world accessible from w. -/
def NecessaryReasonAt (m : ExplanationProfile W B R)
    (w : W) (r : R) : Prop :=
  ∀ v, m.reality.ontic.frame.access w v → m.reasonPresent v r

/-- A reason's sufficiency necessitates a particular individual's existence,
as opposed to merely offering an explanation where that individual exists.
This is a substantive, separate assumption. -/
def NecessitatesExistenceAt (m : ExplanationProfile W B R)
    (w : W) (r : R) (x : B) : Prop :=
  ∀ v, m.reality.ontic.frame.access w v →
    m.reasonPresent v r → m.reality.ontic.ExistsAt v x

/-- Necessity of the reason plus necessitating explanatory sufficiency makes
the individual necessary (relative to the specified accessibility frame). -/
theorem necessaryReasonAndNecessitation
    (m : ExplanationProfile W B R) (w : W) (r : R) (x : B)
    (hr : NecessaryReasonAt m w r)
    (hs : NecessitatesExistenceAt m w r x) :
    NecessaryAt m.reality.ontic w x := by
  intro v hv
  exact hs v hv (hr v hv)

/-- An actually contingent individual cannot have a simultaneously necessary
reason which necessitates that *particular* individual's existence.
This contradicts only the stronger necessitation reading, not explanatory
relations that are deliberately non-entailing or include contingent factors. -/
theorem contingentExcludesNecessaryNecessitatingReason
    (m : ExplanationProfile W B R) (w : W) (r : R) (x : B)
    (hc : ContingentAt m.reality.ontic w x)
    (hr : NecessaryReasonAt m w r)
    (hs : NecessitatesExistenceAt m w r x) : False := by
  rcases hc with ⟨_, v, hv, hAbsent⟩
  exact hAbsent (hs v hv (hr v hv))

/-- Every concrete being in the two-world rival is explained by the same
always-true reason token, but that explanation token is not an object in the
concrete domain. It is NOT claimed to be causally productive or a complete
metaphysical explanation, precisely because no modal sufficiency is assumed. -/
def abstractReasonRival : ExplanationProfile Bool (Bool × Bool) Unit where
  reality := boundaryRival
  reasonPresent := fun _ _ => True
  explains := fun w _ x => boundaryRival.ontic.ExistsAt w x

theorem abstractReasonRivalSound : ExplanationSound abstractReasonRival := by
  intro w r x h
  exact ⟨True.intro, True.intro, h⟩

/-- No actual concrete being lacks a locally assigned explanation token. -/
theorem abstractReasonRivalCoverage : LocallyExplained abstractReasonRival := by
  intro w x _ hExists
  exact ⟨(), True.intro, hExists⟩

/-- The one reason token is available in every accessible world. -/
theorem abstractReasonRivalNecessaryReason :
    ∀ w, NecessaryReasonAt abstractReasonRival w () := by
  intro w v _
  trivial

/-- Nonetheless the profile has no de re necessary concrete individual. -/
theorem abstractReasonRivalNoNecessaryConcrete :
    ¬ NecessaryConcreteAt abstractReasonRival.reality false :=
  boundaryRivalNoNecessary

/-- The rival's abstract token does NOT necessitate the existence of its
contingent actual root. Otherwise contingency would contradict the general
necessitation theorem. -/
theorem abstractReasonRivalNonnecessitating :
    ¬ NecessitatesExistenceAt abstractReasonRival false ()
      (false, false) := by
  intro hNecessitates
  have hc : ContingentAt boundaryRival.ontic false (false, false) :=
    boundaryRivalAllContingent false (false, false) rfl
  exact contingentExcludesNecessaryNecessitatingReason
    abstractReasonRival false () (false, false) hc
    (abstractReasonRivalNecessaryReason false) hNecessitates

/-- An explicit combined witness: every world has concrete existents and
locally sound explanations, the explanation reason itself is necessary, but
no necessary *concrete individual* follows. In this profile, 'explains'
is intentionally not a necessitating/existentially productive relation. -/
theorem abstractReasonCoverageInsufficient :
    ExplanationSound abstractReasonRival ∧
    LocallyExplained abstractReasonRival ∧
    (∀ w, NecessaryReasonAt abstractReasonRival w ()) ∧
    (∀ w, InhabitedAt abstractReasonRival.reality w) ∧
    ¬ NecessaryConcreteAt abstractReasonRival.reality false := by
  exact ⟨abstractReasonRivalSound, abstractReasonRivalCoverage,
    abstractReasonRivalNecessaryReason, boundaryRivalInhabited,
    abstractReasonRivalNoNecessaryConcrete⟩

end TruthCore.Causality.BruteFoundationExplanations
