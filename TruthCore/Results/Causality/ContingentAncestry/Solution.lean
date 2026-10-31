import TruthCore.Causality.ContingentAncestry
import TruthCore.Models.ContingentAncestry
import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution

namespace TruthCore.Results.Causality.ContingentAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ContingentAncestry
open TruthCore.Explanation.ExistencePSR (ExistenceFact)
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)

/-- Bare necessary existence requires founded descent only among contingent
ancestors. Do not strengthen this to a root/underivedness conclusion. -/
theorem necessaryAncestor {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hFounded : ContingentConeFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryAncestor m w selected := by
  cases hEM (NecessaryAncestor m w selected) with
  | inl h => exact h
  | inr hNone =>
    have allContingent : ∀ x, Cone m w selected x → ContingentAt m.ontic w x := by
      intro x hCone
      refine ⟨hCone.1.2, ?_⟩
      cases hEM (∃ v, m.ontic.frame.access w v ∧ ¬ m.ontic.ExistsAt v x) with
      | inl h => exact h
      | inr hNoAbsence =>
        apply False.elim
        apply hNone
        refine ⟨x, hCone, ?_⟩
        intro v hv
        cases hEM (m.ontic.ExistsAt v x) with
        | inl h => exact h
        | inr h => exact False.elim (hNoAbsence ⟨v, hv, h⟩)
    apply False.elim
    apply TruthCore.Results.Explanation.ExplanatoryAdequacy.forced
      (A := existenceArena m) (a := w) (S := coneFacts m w selected)
      (x := ExistenceFact.fact selected)
      ⟨hActual, Relation.ReflTransGen.refl⟩
      (allContingent selected ⟨hActual, Relation.ReflTransGen.refl⟩) hFounded
    intro f hf hContingent noContingentReason
    cases f with
    | fact target =>
      obtain ⟨source, hGround⟩ := hDep target hf hContingent
      have hSourceCone : Cone m w selected source :=
        ⟨⟨hGround.1, hGround.2.1⟩, Relation.ReflTransGen.head hGround hf.2⟩
      exact noContingentReason (.fact source) hSourceCone ⟨hf.1, hGround⟩
        (allContingent source hSourceCone)

theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hActual : ActualConcrete m w selected)
    (hFounded : ContingentConeFounded m w selected)
    (hDep : ConeContingentGrounded m w selected)
    (hEM : ExcludedMiddle) : NecessaryConcreteAt m w := by
  obtain ⟨ancestor, hCone, hNecessary⟩ :=
    necessaryAncestor m w selected hActual hFounded hDep hEM
  exact ⟨ancestor, hCone.1.1, hCone.1.2, hNecessary⟩

/-- Expose the strengthening relation as a typed corpus edge. -/
theorem contingentFoundationOfFull {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hWF : ConeWellFounded m w selected) : ContingentConeFounded m w selected := by
  have lift : ∀ a : {x // Cone m w selected x},
      Acc (fun a b : {x // Cone m w selected x} => m.grounds w a.val b.val) a →
      Acc (ContingentReason (existenceArena m) w (coneFacts m w selected)) (.fact a.val) := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      apply Acc.intro
      intro reason hReason
      cases reason with
      | fact source =>
        exact ih ⟨source, hReason.1⟩ hReason.2.2.1.2.2.2
  constructor
  intro fact
  apply Acc.intro
  intro reason hReason
  cases reason with
  | fact source => exact lift ⟨source, hReason.1⟩ (hWF.apply _)

theorem foundationComparison : FoundationComparison := by
  intro W B m w selected hWF
  exact contingentFoundationOfFull m w selected hWF

/-- Strict weakening and the boundary of the new conclusion. -/
theorem strictness : TruthCore.Models.ContingentAncestry.Strictness := by
  exact TruthCore.Models.ContingentAncestry.strictness


end TruthCore.Results.Causality.ContingentAncestry
