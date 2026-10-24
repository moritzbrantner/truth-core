import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover)

/-- Uniqueness of the first mover moved by none without the every-perfection
bridge: the *quarta via* gives a maximal being `m`, and every first mover moved
by none is `m`, so any two are the same. A second derivation of the #159 gap
statement `AtMostOneFirstUnmovedMover`, beside q.11 a.3 (#166). -/
theorem oneFirstMoverViaMaximeEns {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hApplied : CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns
