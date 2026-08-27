import TruthCore.Greek.Aristotle.Physics.BookII.Chapter3

namespace TruthCore.Results.Aristotle.Physics.MultipleProperCauses

open TruthCore.Greek.Aristotle.Physics

/-- Several causal modes permit several proper causes of one effect. -/
theorem oneEffectHasMultipleProperCauses
    (CausesHaveSeveralModes OneEffectHasMultipleProperCauses : Prop)
    (hModes : CausesSaidInSeveralModesReading CausesHaveSeveralModes)
    (hPermit :
      SeveralModesPermitMultipleProperCausesReading
        CausesHaveSeveralModes OneEffectHasMultipleProperCauses) :
    OneEffectMultipleProperCausesReading OneEffectHasMultipleProperCauses := by
  sorry

end TruthCore.Results.Aristotle.Physics.MultipleProperCauses
