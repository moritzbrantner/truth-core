import TruthCore.Case.Catholicism.StageOne
namespace TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
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
  -- INF-CATHOLICISM-STAGE1-FIRST-UNMOVED-MOVER-EXISTS (disjunctive syllogism)
  have hExists : ThereIsAFirstUnmovedMover MovedIn MovesIn := by
    cases hExcludedMiddle with
    | inl h => exact h
    | inr hNone => exact absurd hNone hFirstWay
  -- INF-CATHOLICISM-STAGE1-GOD-EXISTS
  obtain ⟨f, hf⟩ := hExists
  exact ⟨f, hIdentify f hf (hPureAct f hf) (fun g hg => hUnique g f hg hf)⟩
end TruthCore.Results.Case.Catholicism.StageOneFromPrimaVia
