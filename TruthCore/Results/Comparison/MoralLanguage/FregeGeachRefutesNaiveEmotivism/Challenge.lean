import TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP.Solution
namespace TruthCore.Results.Comparison.MoralLanguage.FregeGeachRefutesNaiveEmotivism
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism
theorem fregeGeachRefutesNaiveEmotivism {Sentence Ctx Meaning Attitude : Type}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop)
    (ValidMP : Sentence → Sentence → Prop) (free antecedent : Ctx) (p q : Sentence)
    (hFree : FreeMoralAssertionExpressesAttitudeReading Moral Expresses free)
    (hAntecedent : AntecedentLacksFreeStandingAttitudeReading Expresses free antecedent p)
    (hFrege : ValidityRequiresConstantMeaningReading ValidMP meaning free antecedent)
    (hValid : GeachModusPonensValidReading ValidMP p q)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    EmotivistMeaningFails Moral meaning Expresses := by
  sorry
end TruthCore.Results.Comparison.MoralLanguage.FregeGeachRefutesNaiveEmotivism
