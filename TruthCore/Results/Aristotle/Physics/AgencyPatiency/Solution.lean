import TruthCore.Greek.Aristotle.Physics

namespace TruthCore.Results.Aristotle.Physics.AgencyPatiency

open TruthCore.Greek.Aristotle.Physics

/--
If treating agency and patiency as distinct motions would yield two simultaneous alterations
toward one form, and such a double alteration is impossible, then they are not two distinct
underlying motions.
-/
theorem agencyPatiencyNotDistinctMotions
    (AgencyPatiencyAreDistinctMotions : Prop)
    (TwoAlterationsTowardOneForm : Prop)
    (hConsequence :
      DistinctAgencyPatiencyWouldDoubleAlterationReading
        AgencyPatiencyAreDistinctMotions TwoAlterationsTowardOneForm)
    (hImpossible :
      TwoAlterationsTowardOneFormImpossibleReading TwoAlterationsTowardOneForm) :
    AgencyPatiencyNotDistinctMotionsReading AgencyPatiencyAreDistinctMotions := by
  intro hDistinct
  exact hImpossible (hConsequence hDistinct)

end TruthCore.Results.Aristotle.Physics.AgencyPatiency
