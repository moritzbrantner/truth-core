import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter7

namespace TruthCore.Results.Aristotle.Physics.VoidNotNecessaryForMotion

open TruthCore.Greek.Aristotle.Physics

/-- Qualitative change in a full body refutes the alleged necessity of void for motion. -/
theorem voidNotNecessaryForMotion
    (FullBodyCanQualitativelyChange VoidNecessaryForMotion : Prop)
    (hChange : FullBodyCanQualitativelyChangeReading FullBodyCanQualitativelyChange)
    (hBridge :
      FullChangeShowsVoidUnnecessaryForMotionReading
        FullBodyCanQualitativelyChange VoidNecessaryForMotion) :
    VoidNotNecessaryForMotionReading VoidNecessaryForMotion := by
  sorry

end TruthCore.Results.Aristotle.Physics.VoidNotNecessaryForMotion
