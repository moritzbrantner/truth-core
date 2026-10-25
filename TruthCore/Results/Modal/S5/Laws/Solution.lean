import TruthCore.Modal.S5Research
import TruthCore.Results.Modal.K.Laws.Solution
import TruthCore.Results.Modal.B.Laws.Solution
import TruthCore.Results.Modal.B.NecessarySymmetry.Solution
namespace TruthCore.Results.Modal.S5.Laws
open TruthCore.Modal TruthCore.Modal.ResearchFixture TruthCore.Modal.S5Research
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

theorem actual {W : Type} (F : Frame W) (w : W) (hs : S5Frame F)
    (hp : Dia F (MC F allPredicates) w) : MC F allPredicates w := by
  exact TruthCore.Results.Modal.B.Laws.possible_full F w (s5_implies_ktb F hs).2 hp

theorem modes {W : Type} (F : Frame W) (w : W) (hs : S5Frame F) :
    (MC F allPredicates w ↔ Dia F (MC F allPredicates) w) ∧
    (MC F allPredicates w ↔ Box F (MC F allPredicates) w) := by
  refine ⟨⟨?_, actual F w hs⟩, ?_⟩
  · intro h
    exact ⟨w, (s5_implies_ktb F hs).1 w, h⟩
  · exact TruthCore.Results.Modal.B.NecessarySymmetry.checks _ F w (s5_implies_ktb F hs).2

theorem uniform {W : Type} (F : Frame W) (w : W) (hs : S5Frame F)
    (hp : Dia F (MC F allPredicates) w) : ComponentUniform F allPredicates w := by
  have he := identity_separates F allPredicates w trivial (actual F w hs hp)
  intro a b hwa hwb P _
  rw [he a hwa, he b hwb]

theorem consequences {W : Type} (F : Frame W) (w : W) (hs : S5Frame F)
    (hp : Dia F (MC F allPredicates) w) :
    (∀ P : MProp W, Dia F P w ↔ P w) ∧
    (∀ P : MProp W, P w ↔ Box F P w) ∧
    (∀ P : MProp W, ¬ Contingent F P w) := by
  have hm := actual F w hs hp
  have ha := (TruthCore.Results.Modal.K.Laws.full_iff_actuality F w).mp hm
  refine ⟨?_, ?_, fun P => TruthCore.Results.Modal.K.Laws.no_contingency F w P hm⟩
  · intro P
    exact ⟨ha P trivial, fun h => ⟨w, (s5_implies_ktb F hs).1 w, h⟩⟩
  · intro P
    exact ⟨fun h => hm P trivial h, fun h => h w ((s5_implies_ktb F hs).1 w)⟩

theorem checks : Laws := by
  refine ⟨fun _ F w hs => modes F w hs, fun _ F w hs hp => uniform F w hs hp,
    fun _ F w hs hp => consequences F w hs hp, ?_⟩
  intro W F w hs hu hp v
  exact identity_separates F allPredicates w trivial (actual F w hs hp) v (hu w v)
end TruthCore.Results.Modal.S5.Laws
