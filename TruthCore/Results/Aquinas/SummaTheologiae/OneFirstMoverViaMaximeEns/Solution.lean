import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover MaximeEnsIsGod)

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
    (bonum verum nobile esse : Respect) (God : Being → Prop)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hGod : MaximeEnsIsGod InAct MoreIn esse God)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse God)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUARTA-VIA (result AQUINAS-ST-I-Q2-A3-QUARTA-VIA)
  obtain ⟨m, hMax, _⟩ := QuartaVia.quartaVia InAct MoreIn CausesIn bonum verum nobile
    esse hGrades hApproach hTrue hGenus
  -- INF-AQUINAS-FIRST-MOVER-IS-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS)
  have hIdent := FirstMoverIsMaximeEns.firstMoverIsMaximeEns MovedIn MovesIn InAct
    MoreIn CausesIn esse God hGenus hInAct hBeing hGod hApplied hEM
  -- INF-AQUINAS-ONE-FIRST-MOVER-VIA-MAXIME-ENS: both are the maximal being
  intro f g hF hG
  have hf : f = m := hIdent f hF m hMax
  have hg : g = m := hIdent g hG m hMax
  exact hf.trans hg.symm
end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMoverViaMaximeEns
