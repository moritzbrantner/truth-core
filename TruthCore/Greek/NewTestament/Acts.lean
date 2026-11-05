module

public import TruthCore.History.ResurrectionVocabulary

@[expose] public section

namespace TruthCore.Greek.NewTestament.Acts
open TruthCore.History.Resurrection

/-- Acts 1.13-14 includes Jesus' brothers among those persevering in prayer. -/
def ActsBrothersPraying (s : State) : Prop := Reported s .actsBrothersPraying

end TruthCore.Greek.NewTestament.Acts
