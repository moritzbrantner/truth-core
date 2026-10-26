import TruthCore.Logic.Scientism
import TruthCore.Results.Logic.SelfApplication.Dilemma.Solution
namespace TruthCore.Results.Logic.Scientism.StrongDilemma
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Scientism
/-- The scientism dilemma: if scientism's formulation lies in its own scope and
is not empirically established, then if scientism holds its formulation is
not established (horn 1), and if its formulation is established it is a
counterexample, so scientism fails (horn 2). -/
theorem strongScientismDilemma {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (self : Claim) (hScope : ScientismInOwnScope scope self)
    (hNotEmpirical : ScientismNotEmpiricallyEstablished E self) :
    ScientismDilemma E scope self := by
  sorry
end TruthCore.Results.Logic.Scientism.StrongDilemma
