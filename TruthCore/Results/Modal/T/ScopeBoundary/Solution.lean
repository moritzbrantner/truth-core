import TruthCore.Modal.TResearch
import TruthCore.Results.Modal.K.ScopeBoundary.Solution
namespace TruthCore.Results.Modal.T.ScopeBoundary
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.TResearch
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem not_full (w : Bool) : ¬ MC duplicates.frame allPredicates w := by
  intro h
  have he := (K.Laws.full_iff_successors duplicates.frame w).mp h (!w) rfl
  cases w <;> exact Bool.noConfusion he

theorem checks : ScopeBoundary := by
  refine ⟨(fun _ => rfl), K.ScopeBoundary.duplicate_language_all,
    not_full, ?_, ?_, ?_, ?_, ?_, ?_, duplicate_not_extensional, ?_⟩
  · exact ⟨false, rfl, duplicate_language_collapse⟩
  · intro w _; exact K.ScopeBoundary.duplicate_language_all w
  · rintro ⟨w, _, hm⟩; exact not_full w hm
  · intro h; exact not_full false (h false rfl)
  · exact K.ScopeBoundary.checks.2.2.2.2.1
  · exact K.ScopeBoundary.checks.2.2.2.2.2.1
  · intro h; exact Bool.noConfusion h
end TruthCore.Results.Modal.T.ScopeBoundary
