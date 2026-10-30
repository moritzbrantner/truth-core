import TruthCore.Explanation.NoBruteExistence
import TruthCore.Models.PSR
namespace TruthCore.Results.Explanation.NoBruteExistence
open TruthCore.Explanation.ExistencePSR
open TruthCore.Explanation.NoBruteExistence

theorem exclusion {World Being : Type} (m : Model World Being) (w : World) :
    ¬ (NoBruteExistenceAt m w ∧ BruteExistenceAt m w) := by
  rintro ⟨hNo, x, hx, hBrute⟩
  exact hBrute (hNo x hx)

theorem coverage {World Being : Type} (m : Model World Being) (w : World)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    NoBruteExistenceAt m w ∨ BruteExistenceAt m w := by
  cases hEM (BruteExistenceAt m w) with
  | inl hb => exact Or.inr hb
  | inr hnb =>
    left
    intro x hx
    cases hEM (∃ r, m.explains w r (.fact x)) with
    | inl hr => exact hr
    | inr hnr => exact False.elim (hnb ⟨x, hx, hnr⟩)

theorem allWorld_iff {World Being : Type} (m : Model World Being) :
    ExistencePSR m ↔ ∀ w, NoBruteExistenceAt m w := by
  exact Iff.rfl

theorem checks {World Being : Type} (m : Model World Being) (w : World)
    (hEM : TruthCore.Logic.ExcludedMiddle) : LocalExistenceBoundary m w := by
  exact ⟨coverage m w hEM, exclusion m w, allWorld_iff m⟩

theorem scopeControl : LocalDoesNotImplyGlobal := by
  let m : Model Bool Bool := {
    ontic := TruthCore.Models.PSR.Intrinsic.model.ontic
    explains := fun w r f => match f with
      | .fact x => w = false ∧ x = false ∧ r = .intrinsic x }
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · intro w x r h
    exact h.2.1
  · intro x hx
    exact ⟨.intrinsic x, rfl, hx, rfl⟩
  · refine ⟨false, rfl, ?_⟩
    rintro ⟨r, hr⟩
    exact Bool.noConfusion hr.1
  · intro h
    obtain ⟨r, hr⟩ := h true false rfl
    exact Bool.noConfusion hr.1
end TruthCore.Results.Explanation.NoBruteExistence
