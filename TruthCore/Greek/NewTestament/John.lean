import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.John
open TruthCore.History.Resurrection

/-- John 20.19-25 narrates disciples seeing Jesus, rejoicing and telling Thomas. -/
def JohnDisciplesRejoice (s : State) : Prop := Reported s .johnDisciplesRejoice

/-- John 7.3-5 speaks collectively of Jesus' brothers not believing. -/
def JohnBrothersUnbelieving (s : State) : Prop := Reported s .johnBrothersUnbelieving

end TruthCore.Greek.NewTestament.John
