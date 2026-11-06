module
public import TruthCore.Metaethics.MeaningRivalBoundary
@[expose] public section
namespace TruthCore.Results.Metaethics.MeaningRivalBoundary.GuardedNegative
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism
open TruthCore.Metaethics.MeaningRivalBoundary
theorem guardedNegative {Sentence Ctx Meaning Attitude : Type}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop) (free antecedent : Ctx) (p : Sentence)
    (hInvariant : ExpressivistMoralMeaningInvariantReading Moral meaning)
    (hFree : FreeMoralAssertionExpressesAttitudeReading Moral Expresses free)
    (hLoss : AntecedentLacksFreeStandingAttitudeReading Expresses free antecedent p)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    EmotivistMeaningFails Moral meaning Expresses := by
  intro hOccasion
  obtain ⟨a, hExpresses⟩ := hFree p hMoral
  exact hLoss a hExpresses (hOccasion p hMoral free antecedent
    (hInvariant p hMoral free antecedent) a hExpresses)
end TruthCore.Results.Metaethics.MeaningRivalBoundary.GuardedNegative
