import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.Clement.FirstCorinthians
open TruthCore.History.Resurrection

/-- 1 Clement 5.2-7 praises Peter's and Paul's suffering/endurance. It does
not establish the sincerity of every disciple's appearance experience. -/
def ClementEndurance (s : State) : Prop := Reported s .clementEndurance

/-- 1 Clement 42.3 describes apostles as assured through the resurrection. -/
def ClementApostolicConviction (s : State) : Prop := Reported s .clementApostolicConviction

end TruthCore.Greek.Clement.FirstCorinthians
