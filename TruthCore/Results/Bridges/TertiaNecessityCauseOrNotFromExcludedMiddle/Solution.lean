import TruthCore.Logic.ExcludedMiddle
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
namespace TruthCore.Results.Bridges.TertiaNecessityCauseOrNotFromExcludedMiddle
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401), an instance of excluded middle: the tertia via's case split
(`STMT-NECESSARY-HAS-CAUSE-OF-NECESSITY-OR-NOT`: every necessary being either
has a cause of its necessity from another or does not) is one instance of
excluded middle (`STMT-EXCLUDED-MIDDLE`) per necessary being. The proof only
instantiates the premise; it connects the case split to the self-evident
principle and closes nothing by its own content. -/
theorem necessaryHasCauseOfNecessityOrNot {Being Time : Type}
    (Possible : (Time → Prop) → Prop) (IsAt : Being → Time → Prop)
    (CausesNecessityOf : Being → Being → Prop)
    (hExcludedMiddle : TruthCore.Logic.ExcludedMiddle) :
    NecessaryHasCauseOfNecessityOrNotReading Possible IsAt CausesNecessityOf :=
  fun x _ => hExcludedMiddle (HasCauseOfNecessityAliunde CausesNecessityOf x)
end TruthCore.Results.Bridges.TertiaNecessityCauseOrNotFromExcludedMiddle
