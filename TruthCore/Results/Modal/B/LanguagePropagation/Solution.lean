import TruthCore.Modal.BResearch
namespace TruthCore.Results.Modal.B.LanguagePropagation
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.BResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box)

theorem checks : LanguagePropagation := by
  intro W F D w hEM hNeg hBox hSym ⟨v, hv, hc⟩ P hp hw
  have hBack := hSym w v hv
  have hAgree := collapse_agreement F D v hEM hNeg hc w hBack
  have hPv := (hAgree P hp).mpr hw
  have hBP : Box F P v := hc P hp hPv
  exact hc (Box F P) (hBox P hp) hBP w hBack
end TruthCore.Results.Modal.B.LanguagePropagation
