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
  -- INF-HUME-NO-MUTUAL-CAUSE-FROM-NO-LOOPS
  intro x y _ ⟨hxy, hyx⟩
  exact noLoops x (Relation.TransGen.head hxy (Relation.TransGen.single hyx))

/-- The converse fails, so Hume's maxim is strictly weaker than the premise and
does not state it: a self-cause satisfies the maxim (which speaks only of
another), and so does a three-step cycle on `Fin 3`, which has no two-step
cycle. -/
theorem notConverse :
    (¬ ∀ (Entity : Type) (cause : Entity → Entity → Prop),
      NoMutualCauseReading cause → NoCausalLoops cause) ∧
    (¬ ∀ (cause : Fin 3 → Fin 3 → Prop), (∀ x, ¬ cause x x) →
      NoMutualCauseReading cause → NoCausalLoops cause) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact h Unit (fun _ _ => True) (fun x y hne _ => hne (Subsingleton.elim x y)) ()
      (Relation.TransGen.single trivial)
  · intro h
    have hIrrefl : ∀ x : Fin 3, ¬ (x = x + 1) := by decide
    have hNoMutual : ∀ x y : Fin 3, x ≠ y → ¬ (y = x + 1 ∧ x = y + 1) := by decide
    refine h (fun a b => b = a + 1) hIrrefl hNoMutual 0 ?_
    exact Relation.TransGen.head (b := 1) rfl
      (Relation.TransGen.head (b := 2) rfl (Relation.TransGen.single rfl))

end TruthCore.Results.Comparison.HumeCauseAsymmetry
