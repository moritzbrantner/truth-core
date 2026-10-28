import TruthCore.Modal.ActualistDomains
import TruthCore.Models.PSR

namespace TruthCore.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference

/-- Transparent package of two exact domain correspondences, their contingency
consequence, and failures in one unchanged populated universal-frame ontology.
No metaphysical possibility or actual domain policy is asserted. -/
def ActualistDomainCertificate : Prop :=
  (∀ (W B : Type) (m : Ontic W B),
    BoxAllToAllBox m ↔ IncreasingDomains m) ∧
  (∀ (W B : Type) (m : Ontic W B),
    AllBoxToBoxAll m ↔ DecreasingDomains m) ∧
  (∀ (W B : Type) (m : Ontic W B), IncreasingDomains m →
    ∀ w x, ¬ ContingentAt m w x) ∧
  (let m := TruthCore.Models.PSR.ContingentOnly.model.ontic
   (∀ w v, m.frame.access w v) ∧ NecessaryAt m false false ∧
   ContingentAt m false true ∧
   ¬ IncreasingDomains m ∧ ¬ DecreasingDomains m ∧
   ¬ BoxAllToAllBox m ∧ ¬ AllBoxToBoxAll m)
end TruthCore.Modal.ActualistDomains
