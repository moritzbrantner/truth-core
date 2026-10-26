import TruthCore.Logic.Scientism
import TruthCore.Results.Logic.SelfApplication.DemarcationTest.Solution
namespace TruthCore.Results.Logic.Scientism.WeakDemarcation
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Scientism
/-- Second-order test for weak (restricted) scientism. If the weak thesis is in
the strong scope and not empirically established: inside its own domain it is
not established if it holds (the strong horn 1 returns); outside, if
established, it concedes a non-empirically established claim and strong
scientism fails. -/
theorem weakScientismDemarcation {Claim : Type} (E : EpistemicFrame Claim)
    (scope : Claim → Prop) (D : Norm.Demarcation Claim) (w : Claim)
    (hScope : WeakThesisInStrongScope scope w)
    (hNotEmpirical : WeakThesisNotEmpiricallyEstablished E w) :
    WeakScientismDemarcationOutcome E scope D w := by
  have hTest := TruthCore.Results.Logic.SelfApplication.DemarcationTest.demarcationTest
    Claim (scientismNorm E scope) D E.established w hScope hNotEmpirical
  constructor
  · intro hIn hWeak
    exact (hTest.1 hIn).1 hWeak
  · intro hOut hEst
    have hOutside := hTest.2 hOut hEst
    exact ⟨⟨w, hEst, hNotEmpirical⟩, hOutside.2⟩
end TruthCore.Results.Logic.Scientism.WeakDemarcation
