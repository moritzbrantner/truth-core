import TruthCore.Greek.Aristotle.Physics.BookIV.Chapter8

namespace TruthCore.Results.Aristotle.Physics.NoSeparatedVoid

open TruthCore.Greek.Aristotle.Physics

/-- Separated void would permit unlimited coincident magnitudes, which Aristotle rejects. -/
theorem noSeparatedVoid
    (SeparatedVoidExists ArbitrarilyManyEqualMagnitudesCoincide : Prop)
    (hConsequence :
      SeparatedVoidEntailsUnlimitedCoincidenceReading
        SeparatedVoidExists ArbitrarilyManyEqualMagnitudesCoincide)
    (hImpossible :
      UnlimitedEqualMagnitudeCoincidenceImpossibleReading
        ArbitrarilyManyEqualMagnitudesCoincide) :
    SeparatedVoidDoesNotExistReading SeparatedVoidExists := by
  intro hVoid
  exact hImpossible (hConsequence hVoid)

end TruthCore.Results.Aristotle.Physics.NoSeparatedVoid
