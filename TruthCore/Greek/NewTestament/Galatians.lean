import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.Galatians
open TruthCore.History.Resurrection

/-- Gal 1.13-24 reports the speaker's persecuting past and present preaching. -/
def PaulPersecutorPreacher (s : State) : Prop := Reported s .paulPersecutorPreacher

/-- Gal 1.18-19 names James, the Lord's brother, as one Paul saw. -/
def PaulMetJames (s : State) : Prop := Reported s .paulMetJames

end TruthCore.Greek.NewTestament.Galatians
