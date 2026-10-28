import TruthCore.Modal.ActualistDomainsCertificate
namespace TruthCore.Results.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.ActualistDomains
variable {W B : Type}
theorem boxAllToAllBox_iff (m : Ontic W B) :
    BoxAllToAllBox m ↔ IncreasingDomains m := by sorry
theorem allBoxToBoxAll_iff (m : Ontic W B) :
    AllBoxToBoxAll m ↔ DecreasingDomains m := by sorry
theorem increasing_excludes_contingency (m : Ontic W B)
    (h : IncreasingDomains m) : ∀ w x, ¬ ContingentAt m w x := by sorry
theorem checks : ActualistDomainCertificate := by sorry
end TruthCore.Results.Modal.ActualistDomains
