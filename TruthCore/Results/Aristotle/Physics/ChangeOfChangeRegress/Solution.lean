import TruthCore.Greek.Aristotle.Physics.BookV.Chapter2

namespace TruthCore.Results.Aristotle.Physics.ChangeOfChangeRegress

open TruthCore.Greek.Aristotle.Physics

/-- Aristotle's regress argument against per se change of change in *Physics* V.2,
225b34-226a6. -/
theorem changeOfChangeRegress
    (PerSeChangeOfChange InfiniteRegress AnythingCanBecomeMoveOrChange : Prop)
    (hRegress :
      ChangeOfChangeLeadsToInfiniteRegressReading PerSeChangeOfChange InfiniteRegress)
    (hNoFirst :
      InfiniteRegressPreventsAnyChangeReading
        InfiniteRegress AnythingCanBecomeMoveOrChange) :
    ChangeOfChangePreventsAnyChangeReading
      PerSeChangeOfChange AnythingCanBecomeMoveOrChange := by
  intro hChangeOfChange
  exact hNoFirst (hRegress hChangeOfChange)

end TruthCore.Results.Aristotle.Physics.ChangeOfChangeRegress
