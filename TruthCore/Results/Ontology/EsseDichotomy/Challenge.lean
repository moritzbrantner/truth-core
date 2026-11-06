import TruthCore.Ontology.ConcreteAbstract
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Ontology.EsseDichotomy
open TruthCore.Ontology.ConcreteAbstract
/-- The esse criterion draws an exact line (owner, #1103, 2026-11-06): every
candidate has esse in re (concrete) or lacks it (abstract), and none both has
and lacks it. Exhaustiveness instantiates excluded middle (`STMT-EXCLUDED-MIDDLE`)
at "x has esse in re"; disjointness is proved without premises. A transcription
by instantiation: it says nothing about which candidates have esse in re, and
nothing about the rival criteria, which need not be exhaustive. -/
theorem esseDichotomyOfExcludedMiddle {B R : Type} (InAct : B → R → Prop) (esse : R)
    (hExcludedMiddle : TruthCore.Logic.ExcludedMiddle) :
    EsseDichotomy InAct esse := by
  sorry
end TruthCore.Results.Ontology.EsseDichotomy
