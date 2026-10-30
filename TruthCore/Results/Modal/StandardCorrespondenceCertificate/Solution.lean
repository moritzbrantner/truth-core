import TruthCore.Modal.StandardCorrespondenceCertificate
import TruthCore.Results.Modal.StandardCorrespondence.Solution

namespace TruthCore.Results.Modal.StandardCorrespondenceCertificate
/-- Assembly only: the separately frozen T/D correspondences, no new discovery. -/
theorem certificate : TruthCore.Modal.StandardCorrespondenceCertificate := by
  exact ⟨fun _ F => StandardCorrespondence.t_iff_reflexive F,
    fun _ F => StandardCorrespondence.d_iff_serial F⟩
end TruthCore.Results.Modal.StandardCorrespondenceCertificate
