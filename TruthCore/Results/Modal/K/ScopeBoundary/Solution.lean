import TruthCore.Results.Modal.K.Laws.Solution
namespace TruthCore.Results.Modal.K.ScopeBoundary
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.KResearch
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)

theorem duplicate_language_all (w : Bool) :
    MC duplicates.frame (expressible duplicates.frame duplicates.valuation) w := by
  cases w with
  | false => exact duplicate_language_collapse
  | true =>
    rintro P ⟨p, rfl⟩ hp v _
    cases v with
    | false => exact (duplicates_constant p).mpr hp
    | true => exact hp

theorem duplicate_not_full : ¬ MC duplicates.frame allPredicates false := by
  intro h
  exact Bool.noConfusion ((Laws.full_iff_successors _ _).mp h true rfl)

theorem checks : ScopeBoundary := by
  refine ⟨duplicate_language_collapse, duplicate_not_full,
    ⟨false, rfl, duplicate_language_collapse⟩,
    (fun v _ => duplicate_language_all v), ?_, ?_, duplicate_not_extensional, ?_⟩
  · rintro P ⟨p, rfl⟩ ⟨v, _, hp⟩
    cases v with
    | false => exact hp
    | true => exact (duplicates_constant p).mpr hp
  · intro h
    exact duplicate_not_full ((Laws.full_iff_actuality _ _).mpr h)
  · intro W F D w hEM hNeg hExt hMC
    apply (Laws.full_iff_successors F w).mpr
    intro v hv
    exact (extensional_separates F D w hEM hNeg hExt hMC v hv).symm
end TruthCore.Results.Modal.K.ScopeBoundary
