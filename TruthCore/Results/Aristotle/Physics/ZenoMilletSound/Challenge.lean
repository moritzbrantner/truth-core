import TruthCore.Greek.Aristotle.Physics.BookVII.Chapter5

namespace TruthCore.Results.Aristotle.Physics.ZenoMilletSound
open TruthCore.Greek.Aristotle.Physics

theorem zenoMilletSound
    (EveryMilletPartMakesSound EveryMilletPartMovesAir : Prop)
    (hSoundAir : EveryMilletPartSoundingEntailsEveryPartMovesAirReading
      EveryMilletPartMakesSound EveryMilletPartMovesAir)
    (hThreshold : NotEveryMilletPartMovesAirReading
      EveryMilletPartMovesAir) :
    NotEveryMilletPartMakesSoundReading
      EveryMilletPartMakesSound := by
  sorry

end TruthCore.Results.Aristotle.Physics.ZenoMilletSound
