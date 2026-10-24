import TruthCore.Case.Catholicism.StageOneConvergence
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (NecessaryBeingHasBeing CauseOfNecessaryBeingCausesItsNecessity
  NecessaryPerSeIsMaximeEns)
theorem necessaryPerSeIsMaximeEns {Being Time Respect : Type}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing Possible IsAt InAct esse)
    (hCauseNecessity :
      CauseOfNecessaryBeingCausesItsNecessity Possible IsAt CausesIn esse CausesNecessityOf)
    (hEM : ExcludedMiddle) :
    NecessaryPerSeIsMaximeEns Possible IsAt CausesNecessityOf InAct MoreIn esse := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSeIsMaximeEns
