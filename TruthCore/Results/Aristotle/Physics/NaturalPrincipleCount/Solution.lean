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
  rcases hCases with hOne | hTwo | hThree | hMore
  · exact False.elim (hNotOne hOne)
  · exact Or.inl hTwo
  · exact Or.inr hThree
  · exact False.elim (hNotMore hMore)

end TruthCore.Results.Aristotle.Physics.NaturalPrincipleCount
