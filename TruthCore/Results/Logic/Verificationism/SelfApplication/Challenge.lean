import TruthCore.Logic.Verificationism
import TruthCore.Results.Logic.SelfApplication.Dilemma.Solution
namespace TruthCore.Results.Logic.Verificationism.SelfApplication
open TruthCore.Logic.Verificationism
open TruthCore.Logic.SelfApplication
/-- The verificationist self-application dilemma: if the principle's formulation lies in its own scope and is neither analytic nor verifiable, then if the principle holds the formulation is not meaningful, and if the formulation is meaningful the principle fails. -/
theorem verificationistDilemma {L : Language} (F : Frame L)
    (meaningful scope verifiable : L.Sentence → Prop) (v : L.Sentence)
    (hScope : PrincipleInOwnScope scope v) (hNotAnalytic : PrincipleNotAnalytic F v)
    (hNotVerifiable : PrincipleNotVerifiable verifiable v) :
    VerificationistDilemma F meaningful scope verifiable v := by
  sorry
end TruthCore.Results.Logic.Verificationism.SelfApplication
