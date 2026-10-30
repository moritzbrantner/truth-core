import TruthCore.Modal.ConvergenceCertificate
import TruthCore.Results.Modal.Convergence.Solution

namespace TruthCore.Results.Modal.ConvergenceCertificate
universe u v

/-- Assembly of the nine frozen correspondence helpers; not new discovery. -/
theorem certificate : TruthCore.Modal.ConvergenceCertificate.{u, v} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ F a b => Convergence.exactPath_zero F a b
  · exact fun _ F n a b => Convergence.exactPath_succ F n a b
  · exact fun _ _ F V φ n a => Convergence.iterBox_semantics F V φ n a
  · exact fun _ _ F V φ n a => Convergence.iterDiamond_semantics F V φ n a
  · exact fun _ _ F h i j k hc φ => Convergence.convergence_sound F h i j k hc φ
  · exact fun _ F h i j k => Convergence.convergence_iff_valid F h i j k
  · exact fun _ F => Convergence.axiom4_correspondence F
  · exact fun _ F => Convergence.axiomB_correspondence F
  · exact fun _ F => Convergence.axiom5_correspondence F

end TruthCore.Results.Modal.ConvergenceCertificate
