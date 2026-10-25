import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.FirstCorinthians
open TruthCore.History.Resurrection

/-- 1 Cor 15.3-8 reports received/transmitted death, burial, rising and
appearances to Cephas, the Twelve, more than 500, James, apostles and Paul.
No calendar date or conversion of James is asserted by this report. -/
def PaulReceivedAppearances (s : State) : Prop := Reported s .paulReceivedAppearances

end TruthCore.Greek.NewTestament.FirstCorinthians
