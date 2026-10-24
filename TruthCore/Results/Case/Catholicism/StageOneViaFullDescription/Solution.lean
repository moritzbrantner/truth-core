import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Case.Catholicism.StageOne
namespace TruthCore.Results.Case.Catholicism.StageOneViaFullDescription
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Stage 1, "God exists", with the skeleton's `IsGod` linked to the *Summa*'s
God through the fuller nominal definition (owner decisions on #143,
2026-10-24). The predicate the fuller definition applies is `IsGod` itself: a
being that meets what the name signifies is God in the proper sense (q.2 a.2
ad 2, q.13 a.8 ad 2). The bare identification premise
`UniquePureActFirstMoverIsGod`, the pure-act bridges and q.11 a.3 are not
used.

There is a first mover moved by none (the *prima via* and the excluded-middle
instance). There is something maximal in being (the *quarta via*). The maximum
in being is God by version (a) of the discharge
(`AQUINAS-ST-I-Q2-A3-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION`). The first mover
is that maximum (`AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS`). So the first
mover is God. -/
theorem stageOneViaFullDescription {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (ComponentOf : Being → Being → Prop) (IsGod : Being → Prop)
    (hFirstWay : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsMaximalInBeingReading InAct MoreIn esse ComponentOf)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod)
    (hApplied : CreatedAgentIsAppliedToActByGodReading MovedIn MovesIn CausesIn esse IsGod) :
    GodExists IsGod := by
  -- INF-CATHOLICISM-STAGE1-FIRST-UNMOVED-MOVER-EXISTS (disjunctive syllogism)
  have hExists : ThereIsAFirstUnmovedMover MovedIn MovesIn := by
    cases hExcludedMiddle with
    | inl h => exact h
    | inr hNone => exact absurd hNone hFirstWay
  obtain ⟨f, hf⟩ := hExists
  -- INF-AQUINAS-ST-I-Q2-A3-QUARTA-VIA (result AQUINAS-ST-I-Q2-A3-QUARTA-VIA)
  obtain ⟨m, hMax, _⟩ := TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.quartaVia InAct MoreIn CausesIn bonum verum nobile esse
    hGrades hApproach hTrue hGenus
  -- INF-AQUINAS-MAXIME-ENS-IS-GOD-VIA-FULL-DESCRIPTION (result, version (a))
  have hGod : MaximeEnsIsGod InAct MoreIn esse IsGod :=
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescription.maximeEnsIsGodViaFullDescription InAct MoreIn CausesIn
      esse ComponentOf IsGod hGenus hCauseMore hEM hBeing hPerfections hNoComponent hFull
  -- INF-AQUINAS-FIRST-MOVER-IS-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS)
  have hSame : f = m :=
    TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.firstMoverIsMaximeEns MovedIn MovesIn InAct MoreIn CausesIn esse IsGod
      hGenus hInAct hBeing hGod hApplied hEM f hf m hMax
  -- INF-CATHOLICISM-STAGE1-FIRST-MOVER-IS-GOD
  exact ⟨f, hSame ▸ hGod m hMax⟩

end TruthCore.Results.Case.Catholicism.StageOneViaFullDescription
