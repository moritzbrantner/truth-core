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
  have hFail : ¬ (F.analytic v ∨ verifiable v) := fun h => h.elim hNotAnalytic hNotVerifiable
  have hHorns := TruthCore.Results.Logic.SelfApplication.Dilemma.selfApplicationDilemma
    L.Sentence ⟨scope, fun s => F.analytic s ∨ verifiable s⟩ meaningful v hScope hFail
  exact ⟨hHorns.1, fun hMeaningful => Norm.not_holds_of_counterexample (hHorns.2 hMeaningful)⟩
end TruthCore.Results.Logic.Verificationism.SelfApplication
