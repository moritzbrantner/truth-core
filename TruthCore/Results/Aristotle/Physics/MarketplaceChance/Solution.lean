import TruthCore.Greek.Aristotle.Physics.BookII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.MarketplaceChance

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's marketplace conditions satisfy his stated condition for chance. -/
theorem marketplaceRepaymentByChance
    (RepaymentCouldBeChosenEnd VisitorCameForRepayment
      VisitWasNecessaryOrUsual RepaymentOccurredIncidentally
      RepaymentOccurredByChance : Prop)
    (hCase :
      MarketplaceRepaymentChanceConditionsReading
        RepaymentCouldBeChosenEnd VisitorCameForRepayment
        VisitWasNecessaryOrUsual RepaymentOccurredIncidentally)
    (hRule :
      ExceptionalIncidentalChosenEndImpliesChanceReading
        RepaymentCouldBeChosenEnd VisitorCameForRepayment
        RepaymentOccurredIncidentally VisitWasNecessaryOrUsual
        RepaymentOccurredByChance) :
    MarketplaceRepaymentByChanceReading RepaymentOccurredByChance := by
  rcases hCase with ⟨hPotentialEnd, hNotForRepayment, hExceptional, hIncidental⟩
  exact hRule ⟨hPotentialEnd, hNotForRepayment, hIncidental, hExceptional⟩

end TruthCore.Results.Aristotle.Physics.MarketplaceChance
