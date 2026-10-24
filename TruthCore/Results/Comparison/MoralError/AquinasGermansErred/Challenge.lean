import TruthCore.Comparison.MoralError
namespace TruthCore.Results.Comparison.MoralError.AquinasGermansErred
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Metaethics
theorem aquinasGermansErred {Agent Sentence : Type}
    (Accepts : Agent → Sentence → Prop) (Moral TruthApt Holds : Sentence → Prop)
    (germans : Agent) (robberyNotUnjust : Sentence)
    (hTruthApt : MoralJudgmentsAreTruthAptReading Moral TruthApt)
    (hGermans : GermansHeldRobberyNotUnjustReading Accepts Moral Holds germans robberyNotUnjust) :
    SomeMoralError Accepts Moral TruthApt Holds := by
  sorry
end TruthCore.Results.Comparison.MoralError.AquinasGermansErred
