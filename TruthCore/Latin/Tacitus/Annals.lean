import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Latin.Tacitus.Annals
open TruthCore.History.Resurrection

/-- Tacitus Ann.15.44 reports Christus receiving punishment under Pilate in
Tiberius' reign. Read supplicio adfectus here as execution; the sentence does
not itself specify crucifixion. The crosses later in the chapter concern
Nero's victims. -/
def TacitusExecution (s : State) : Prop := Reported s .tacitusExecution

end TruthCore.Latin.Tacitus.Annals
