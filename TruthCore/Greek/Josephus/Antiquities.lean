import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.Josephus.Antiquities
open TruthCore.History.Resurrection

/-- Josephus Ant.20.200 reports Ananus handing James, brother of Jesus called
Christ, and others over to stoning on a lawbreaking accusation. It does not
report conversion or a refusal to recant resurrection testimony. -/
def JosephusJamesStoned (s : State) : Prop := Reported s .josephusJamesStoned

end TruthCore.Greek.Josephus.Antiquities
