import TruthCore.Modal.ResearchFinite
namespace TruthCore.Results.Modal.ResearchFixture
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
 theorem checks : TruthCore.Modal.ResearchFinite.Checks := by
  refine ⟨?_, @eval_correct, duplicate_language_collapse, duplicate_identity_inadmissible,
    duplicate_not_extensional, inventory_collapse, branching_language_not_collapse,
    branching_full_not_collapse, branching_root_failure, branching_terminal_success,
    branching_witness, branching_possibility⟩
  exact ⟨fun _ F D w => identity_separates F D w,
    fun _ F w => full_iff_hume F w,
    fun _ F D w => extensional_separates F D w⟩
end TruthCore.Results.Modal.ResearchFixture
