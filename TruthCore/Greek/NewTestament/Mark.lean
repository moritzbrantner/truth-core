import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.Mark
open TruthCore.History.Resurrection

/-- Mark 15.24-25,37,44-45 reports crucifixion and death; this is not E0. -/
def MarkCrucifixionDeath (s : State) : Prop := Reported s .markCrucifixionDeath

/-- Mark 14.61-64 attributes an affirmative messianic answer and the Son of
Man at the right hand of Power/clouds to Jesus; identifying this with the
skeleton's divine-authority predicate remains an interpretive premise. -/
def MarkAuthority (s : State) : Prop := Reported s .markAuthority

end TruthCore.Greek.NewTestament.Mark
