import TruthCore.Comparison.ProblemOfEvil
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Comparison.ProblemOfEvil.MoralGroundingAnswerMap
open TruthCore.Comparison.ProblemOfEvil
open TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels

/-- A model of the background and emotivism. Its one sentence says something
is bad, is moral, has no truth value and is not true; nothing is evil, nothing is omnipotent. The motion
part is #151's strong model; it plays no role here. -/
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

theorem moralGroundingCells :
    (∀ s, Background s → Catholic s → ExternalEvilPremise s) ∧
      (∀ s, Background s → Emotivism s → ExternalEvilPremise s → False) := by
  constructor
  · -- INF-CATHOLIC-GROUNDING-ENTAILS-EVIL-PREMISE: a due good is lacking (q.48 a.2),
    -- that lack is evil (q.48 a.3), so "there is evil" is true (q.48 a.2 ad 2).
    intro s _ hCatholic
    obtain ⟨⟨_, hPrivation, hTruth⟩, ⟨x, p, hDue, hLacks⟩, _⟩ := hCatholic
    exact hTruth ⟨x, (hPrivation x).mpr ⟨p, hDue, hLacks⟩⟩
  · -- INF-EMOTIVISM-EVIL-PREMISE-NOT-TRUTH-APT, INF-EMOTIVISM-EXCLUDES-EXTERNAL-EVIL-PREMISE
    intro s ⟨hBadIsMoral, hSaysBad, _⟩ hEmotivism hExternal
    exact hEmotivism.2 s.evilPremise
      (hEmotivism.1 s.evilPremise (hBadIsMoral s.evilPremise hSaysBad)) hExternal

theorem emotivismConsistentWithBackground : ∃ s, Background s ∧ Emotivism s :=
  ⟨emotivistModel, ⟨fun _ h => h, trivial, fun _ _ h => False.elim h⟩, fun _ _ h => h, fun _ _ h => h⟩

end TruthCore.Results.Comparison.ProblemOfEvil.MoralGroundingAnswerMap
