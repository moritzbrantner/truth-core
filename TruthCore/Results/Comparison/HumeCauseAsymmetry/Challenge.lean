import TruthCore.Case.Catholicism.StageOne.CausalFinitism
import TruthCore.Modern.Hume.CauseEffectAsymmetry
namespace TruthCore.Results.Comparison.HumeCauseAsymmetry
open TruthCore.Case.Catholicism.StageOne.CausalFinitism
open TruthCore.Modern.Hume.CauseEffectAsymmetry

/-- The root-path premise STMT-CAUSAL-HISTORY-HAS-NO-LOOPS entails Hume's
asymmetry maxim (*Treatise* I.3.6 §7) for the same relation: if no nonempty
finite causal path returns to its start, nothing is both cause and effect of
another, since `x → y → x` would be such a path. -/
theorem noMutualCauseOfNoCausalLoops {Entity : Type}
    (cause : Entity → Entity → Prop)
    (noLoops : NoCausalLoops cause) :
    NoMutualCauseReading cause := by
  sorry

/-- The converse fails, so Hume's maxim is strictly weaker than the premise and
does not state it: a self-cause satisfies the maxim (which speaks only of
another), and so does a three-step cycle on `Fin 3`, which has no two-step
cycle. -/
theorem notConverse :
    (¬ ∀ (Entity : Type) (cause : Entity → Entity → Prop),
      NoMutualCauseReading cause → NoCausalLoops cause) ∧
    (¬ ∀ (cause : Fin 3 → Fin 3 → Prop), (∀ x, ¬ cause x x) →
      NoMutualCauseReading cause → NoCausalLoops cause) := by
  sorry

end TruthCore.Results.Comparison.HumeCauseAsymmetry
