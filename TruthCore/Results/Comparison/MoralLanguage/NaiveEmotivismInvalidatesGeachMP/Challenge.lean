import TruthCore.Refutations.Emotivism
namespace TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism
theorem naiveEmotivismInvalidatesGeachMP {Sentence Ctx Meaning Attitude : Type}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop)
    (ValidMP : Sentence → Sentence → Prop) (free antecedent : Ctx) (p q : Sentence)
    (hEmotivism : EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses)
    (hFree : FreeMoralAssertionExpressesAttitudeReading Moral Expresses free)
    (hAntecedent : AntecedentExpressesNoAttitudeReading Expresses antecedent p)
    (hFrege : ValidityRequiresConstantMeaningReading ValidMP meaning free antecedent)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    GeachModusPonensInvalid ValidMP p q := by
  sorry
end TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP
