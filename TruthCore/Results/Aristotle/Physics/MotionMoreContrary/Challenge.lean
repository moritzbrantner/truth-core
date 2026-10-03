import TruthCore.Greek.Aristotle.Physics.BookV.Chapter6

namespace TruthCore.Results.Aristotle.Physics.MotionMoreContrary

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's inference in *Physics* V.6, 230b28-231a2. -/
theorem motionMoreContraryThanRest
    (MovingAwayRetainsOriginOnlyQualifiedly
      UnqualifiedRestOppositionWouldMakeContrariesCoexist
      MotionMoreContraryToMotionThanRest : Prop)
    (hPuzzle :
      MovingAwayOriginPuzzleReading MovingAwayRetainsOriginOnlyQualifiedly
        UnqualifiedRestOppositionWouldMakeContrariesCoexist)
    (hTransition :
      MovingAwayPuzzleImpliesMotionMoreContraryReading
        MovingAwayRetainsOriginOnlyQualifiedly
        UnqualifiedRestOppositionWouldMakeContrariesCoexist
        MotionMoreContraryToMotionThanRest) :
    MotionMoreContraryThanRestReading MotionMoreContraryToMotionThanRest := by
  sorry

end TruthCore.Results.Aristotle.Physics.MotionMoreContrary
