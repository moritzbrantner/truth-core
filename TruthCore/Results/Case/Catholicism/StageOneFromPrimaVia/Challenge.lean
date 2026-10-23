import TruthCore.Case.Catholicism.StageOne
namespace TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Stage 1 from the prima via (#151, #156): "God exists" follows from the
prima via conclusion only together with the open gap premises (excluded middle,
uniqueness, pure act, identification). -/
theorem stageOneFromPrimaVia {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PureAct IsGod : Being → Prop)
    (hFirstWay : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn)
    (hExcludedMiddle : FirstUnmovedMoverExistsOrNot MovedIn MovesIn)
    (hUnique : AtMostOneFirstUnmovedMover MovedIn MovesIn)
    (hPureAct : FirstUnmovedMoverIsPureAct MovedIn MovesIn PureAct)
    (hIdentify : UniquePureActFirstMoverIsGod MovedIn MovesIn PureAct IsGod) :
    GodExists IsGod := by
  sorry
end TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
