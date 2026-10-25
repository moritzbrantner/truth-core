import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.Matthew
open TruthCore.History.Resurrection

/-- Matt 28.5-8 reports that the tomb no longer holds Jesus. -/
def MattEmptyTomb (s : State) : Prop := Reported s .mattEmptyTomb

/-- Matt 28.11-15 attributes a theft story to opponents and says it circulated.
It is a Christian report about hostile acknowledgement, not an independently
preserved hostile witness, nor proof that theft or payment occurred. -/
def MattHostileTheftStory (s : State) : Prop := Reported s .mattHostileTheftStory

/-- Matt 28.18 attributes all authority in heaven and earth to Jesus. -/
def MattUniversalAuthority (s : State) : Prop := Reported s .mattUniversalAuthority



end TruthCore.Greek.NewTestament.Matthew
