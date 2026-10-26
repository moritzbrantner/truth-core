import TruthCore.Greek.Aristotle.MetaphysicsIX
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
namespace TruthCore.Results.Bridges.AristPotencyAnalysisNonSimultaneity
open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401): Aristotle's analysis of potency, *Metaphysics* IX.6
(`STMT-POTENCY-IS-UNACTUALIZED-CAPACITY`: to be in potency to `r` is to be able
to be `r` without being `r` actually), entails the prima via's non-simultaneity
premise (`STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`): nothing is in act
and in potency in the same respect. Whatever is in potency to `r` is, by the
analysis, not actually `r`.

`ActPotencyDefinitionalAnalysesConservative` already shows that the analysis is
no stronger than non-simultaneity (given non-simultaneity, some ability
predicate satisfies it). This bridge therefore does not discharge the Aquinas
premise: it moves its openness to the fidelity and truth of the Aristotle
reading, as `docs/act-potency-theory.md` says a definitional analysis would. -/
theorem notActAndPotencyOfPotencyAnalysis {Being Respect : Type}
    (InAct InPotency CanBe : Being → Respect → Prop)
    (hAnalysis : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    NotActAndPotencyInSameRespectReading InAct InPotency := by
  sorry
end TruthCore.Results.Bridges.AristPotencyAnalysisNonSimultaneity
