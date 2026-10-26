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
  sorry
end TruthCore.Results.Logic.Scientism.WeakDemarcation
