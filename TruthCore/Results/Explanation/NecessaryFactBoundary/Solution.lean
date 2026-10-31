import TruthCore.Explanation.NecessaryFactBoundary
import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution

namespace TruthCore.Results.Explanation.NecessaryFactBoundary

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.NecessaryFactBoundary
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)

/-- Use the already proved contingent-reason descent lemma. Excluded middle
selects a positive witness and turns true noncontingency into boxed truth. -/
theorem necessaryReason {W B F : Type} (A : Arena W B F) (a : W)
    (S : F → Prop) (x : F) (hEM : ExcludedMiddle)
    (h : ReasonClosed A a S x) (hc : Contingent A a x) (hf : Founded A a S) :
    NecessaryReasonForMember A a S := by
  rcases hEM (NecessaryReasonForMember A a S) with hn | hn
  · exact hn
  · apply False.elim
    apply TruthCore.Results.Explanation.ExplanatoryAdequacy.forced h.explanandum hc hf
    intro c hs hcc noContingentReason
    obtain ⟨r, he⟩ := h.covered c hs hcc
    have hrS := h.closed r c hs he
    have hr := h.truthful r hrS
    have hnr := noContingentReason r hrS he
    have hbox : ∀ v, Access A a v → A.holds v r := by
      intro v hv
      rcases hEM (A.holds v r) with hvTrue | hvFalse
      · exact hvTrue
      · exact (hnr ⟨hr, v, hv, hvFalse⟩).elim
    exact hn ⟨r, hrS, hr, hbox, c, hs, hcc, he⟩

/-- All conjuncts refer to the same old law interpretation. No modal or
explanatory edge is changed to obtain the negative individual conclusion. -/
theorem lawControl : ReasonClosed law 0 OneSource .target ∧
    Contingent law 0 .target ∧ Founded law 0 OneSource ∧
    NecessaryReasonForMember law 0 OneSource ∧ ∀ b, ¬ NecessaryAt law.ontic 0 b := by
  refine ⟨TruthCore.Results.Explanation.ExplanatoryAdequacy.law_closed,
    TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_target_contingent false,
    TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_founded, ?_, ?_⟩
  · refine ⟨.source true, OneSource.source, Or.inl rfl,
      (fun _ _ => Or.inl rfl), .target, OneSource.target,
      TruthCore.Results.Explanation.ExplanatoryAdequacy.ground_target_contingent false,
      GroundReason.toTarget true (Or.inl rfl)⟩
  · intro b hn
    exact TruthCore.Results.Explanation.ExplanatoryAdequacy.one_ne_zero' (hn 1 True.intro)

/-- Compose positive extraction, the existing modal-collapse cost, and the
matched necessary-law/no-necessary-bearer control. -/
theorem checks : Certificate := by
  refine ⟨?_, lawControl⟩
  intro W B F A a S x hEM h hc hf
  exact ⟨necessaryReason A a S x hEM h hc hf,
    TruthCore.Results.Explanation.ExplanatoryAdequacy.core_necessitate h hc hf⟩

end TruthCore.Results.Explanation.NecessaryFactBoundary
