import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.PrimaryRecipientComparabilityConditions
open TruthCore.Greek.Aristotle.Physics

theorem primaryRecipientComparabilityConditions
    (SameRelevantPrimaryRecipient HorseDogWhitenessComparable
      HorseDogMagnitudeComparable DifferentPrimaryRecipients
      WaterAndVoiceComparable NotEverySubjectReceivesEveryProperty
      EachPropertyHasOwnPrimaryRecipient ComparablesUseSameMeaning
      NoRelevantDifferenceInComparedProperty
      NoRelevantDifferenceInPrimaryRecipient : Prop)
    (hSame : HorseDogComparableThroughSamePrimaryRecipientReading
      SameRelevantPrimaryRecipient HorseDogWhitenessComparable
      HorseDogMagnitudeComparable)
    (hDifferent : WaterVoiceIncomparableDifferentPrimaryRecipientsReading
      DifferentPrimaryRecipients WaterAndVoiceComparable)
    (hSpecific : EachPropertyHasOwnPrimaryRecipientReading
      NotEverySubjectReceivesEveryProperty EachPropertyHasOwnPrimaryRecipient)
    (hTransition : PrimaryRecipientContrastEntailsComparabilityConditionsReading
      SameRelevantPrimaryRecipient DifferentPrimaryRecipients
      EachPropertyHasOwnPrimaryRecipient ComparablesUseSameMeaning
      NoRelevantDifferenceInComparedProperty
      NoRelevantDifferenceInPrimaryRecipient) :
    ComparabilityRequiresSameMeaningPropertyAndSubjectReading
      ComparablesUseSameMeaning NoRelevantDifferenceInComparedProperty
      NoRelevantDifferenceInPrimaryRecipient := by
  sorry

end TruthCore.Results.Aristotle.Physics.PrimaryRecipientComparabilityConditions
