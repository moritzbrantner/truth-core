import TruthCore.Greek.Aristotle.Physics.BookI.Chapter6

namespace TruthCore.Results.Aristotle.Physics.NaturalPrincipleCount

open TruthCore.Greek.Aristotle.Physics

/-- Excluding one and more than three from the enumerated cases leaves two or three. -/
theorem naturalPrincipleCountTwoOrThree
    (OnePrinciple TwoPrinciples ThreePrinciples MoreThanThreePrinciples : Prop)
    (hCases :
      NaturalPrincipleCountCasesReading
        OnePrinciple TwoPrinciples ThreePrinciples MoreThanThreePrinciples)
    (hNotOne : NaturalPrincipleCountNotOneReading OnePrinciple)
    (hNotMore :
      NaturalPrincipleCountNotMoreThanThreeReading MoreThanThreePrinciples) :
    NaturalPrincipleCountTwoOrThreeReading TwoPrinciples ThreePrinciples := by
  sorry

end TruthCore.Results.Aristotle.Physics.NaturalPrincipleCount
