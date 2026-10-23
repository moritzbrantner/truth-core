import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
open TruthCore.English.OConnor
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Comparison.ProblemOfEvil
theorem externalPremiseContradictsEmotivism {Sentence : Type}
    (SaysSomethingBad Moral TruthApt Holds : Sentence → Prop) (evilPremise : Sentence)
    (hEmotivism : MoralStatementsLackTruthValueReading Moral TruthApt)
    (hNoTruth : LackingTruthValueExcludesTruthReading TruthApt Holds)
    (hBadIsMoral : BadnessAscriptionsAreMoralReading SaysSomethingBad Moral)
    (hSaysBad : EvilPremiseSaysSomethingBadReading SaysSomethingBad evilPremise) :
    EvilPremiseNotTrue Holds evilPremise := by
  -- INF-EVIL-PREMISE-IS-MORAL: the evil premise says something is bad, so it is moral.
  have hMoral : Moral evilPremise := hBadIsMoral evilPremise hSaysBad
  -- INF-EMOTIVISM-EVIL-PREMISE-NOT-TRUTH-APT
  have hNotApt : ¬ TruthApt evilPremise := hEmotivism evilPremise hMoral
  -- INF-EMOTIVISM-EXCLUDES-EXTERNAL-EVIL-PREMISE
  exact hNoTruth evilPremise hNotApt

open TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

/-- A model of the background and emotivism: its one sentence says something
is bad, is moral, has no truth value and is not true; nothing is evil and
nothing is omnipotent. The motion part is #151's strong model and plays no
role. It shows that emotivism contradicts the evil premise, not the
background. -/
def emotivistModel : Sig where
  motion := strongModel
  Perfection := Unit
  Sentence := Unit
  Has := fun _ _ => False
  Due := fun _ _ => False
  GoodIn := fun _ _ => False
  Evil := fun _ => False
  God := fun _ => False
  SupremelyGood := fun _ => False
  Omnipotent := fun _ => False
  CanEliminate := fun _ _ => False
  DrawsGoodFrom := fun _ _ _ _ => False
  SaysSomethingBad := fun _ => True
  Moral := fun _ => True
  TruthApt := fun _ => False
  Holds := fun _ => False
  evilPremise := ()

theorem emotivismConsistentWithBackground : ∃ s, Background s ∧ Emotivism s :=
  ⟨emotivistModel, ⟨fun _ h => h, trivial, fun _ _ h => False.elim h⟩, fun _ _ h => h, fun _ _ h => h⟩

end TruthCore.Results.Comparison.ProblemOfEvil.ExternalPremiseVsEmotivism
