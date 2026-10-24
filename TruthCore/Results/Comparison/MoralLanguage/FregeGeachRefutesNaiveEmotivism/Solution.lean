import TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP.Solution
namespace TruthCore.Results.Comparison.MoralLanguage.FregeGeachRefutesNaiveEmotivism
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism

/-- The shared data refute the occasion reading of emotivism. Were it true,
Geach's modus ponens would be invalid (result
`FREGE-GEACH-NAIVE-EMOTIVISM-INVALIDATES-MORAL-MP`); but it is valid. -/
theorem fregeGeachRefutesNaiveEmotivism {Sentence Ctx Meaning Attitude : Type}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop)
    (ValidMP : Sentence → Sentence → Prop) (free antecedent : Ctx) (p q : Sentence)
    (hFree : FreeMoralAssertionExpressesAttitudeReading Moral Expresses free)
    (hAntecedent : AntecedentExpressesNoAttitudeReading Expresses antecedent p)
    (hFrege : ValidityRequiresConstantMeaningReading ValidMP meaning free antecedent)
    (hValid : GeachModusPonensValidReading ValidMP p q)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    EmotivistMeaningFails Moral meaning Expresses := by
  intro hEmotivism
  -- INF-NAIVE-EMOTIVISM-INVALIDATES-GEACH-MP-RESULT (result FREGE-GEACH-NAIVE-EMOTIVISM-INVALIDATES-MORAL-MP)
  have hInvalid : GeachModusPonensInvalid ValidMP p q :=
    NaiveEmotivismInvalidatesGeachMP.naiveEmotivismInvalidatesGeachMP Moral meaning
      Expresses ValidMP free antecedent p q hEmotivism hFree hAntecedent hFrege hMoral
  -- INF-GEACH-VALIDITY-REFUTES-NAIVE-EMOTIVISM
  exact hInvalid hValid

end TruthCore.Results.Comparison.MoralLanguage.FregeGeachRefutesNaiveEmotivism
