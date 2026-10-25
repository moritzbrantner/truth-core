import TruthCore.Modal.BResearch
import TruthCore.Results.Modal.B.Laws.Solution
import TruthCore.Results.Modal.K.ScopeBoundary.Solution
namespace TruthCore.Results.Modal.B.ScopeBoundary
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.BResearch
open TruthCore.Isabelle.AFP.GoedelGod (Dia)

theorem checks : ScopeBoundary := by
  refine ⟨(fun _ => rfl), (fun _ _ h => h), K.ScopeBoundary.duplicate_language_all,
    K.ScopeBoundary.duplicate_not_full, duplicate_not_extensional, ?_, ?_, ?_,
    branching_full_not_collapse, ?_⟩
  · intro W F D w hEM hNeg hExt hSym ⟨v, hv, hc⟩
    have he := extensional_separates F D v hEM hNeg hExt hc w (hSym w v hv)
    have hf := (K.Laws.full_iff_successors F v).mpr
      (fun x hx => (extensional_separates F D v hEM hNeg hExt hc x hx).symm)
    rw [← he]
    exact hf
  · intro w; cases w <;> rfl
  · refine ⟨true, rfl, ?_⟩
    apply (K.Laws.full_iff_successors _ _).mpr
    intro v hv; cases v with
    | false => cases hv
    | true => rfl
  · intro hs; exact Bool.noConfusion (hs false true rfl)
end TruthCore.Results.Modal.B.ScopeBoundary
