import TruthCore.Ethics.HardCaseGoods
import TruthCore.Results.Ethics.HardCaseTyped.Solution
namespace TruthCore.Results.Ethics.HardCaseGoods
open TruthCore.Ethics.HardCaseTyped TruthCore.Ethics.HardCaseGoods

theorem certificate : GoodsOmission := by
  obtain ⟨f, yes, no, _, _, cases, yv, yk, nv, nk, _⟩ :=
    TruthCore.Results.Ethics.HardCaseTyped.certificate.1
  refine ⟨f, (fun c p g => p = .victim ∧ ((c = .violation ∧ g = .bodilyIntegrity) ∨ (c = .killing ∧ g = .life))),
    (fun c a p g => p = .victim ∧ ((c = .violation ∧ a = .violate ∧ g = .bodilyIntegrity) ∨ (c = .killing ∧ a = .kill ∧ g = .life))),
    yes, no, cases, ?_, ?_, ?_, ?_, ?_, ?_, yv, yk, nv, nk⟩
  all_goals decide
end TruthCore.Results.Ethics.HardCaseGoods
