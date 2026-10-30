import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.WithBot
import TruthCore.Causality.WorldSourceRegress
namespace TruthCore.Results.Causality.WorldSourceRegress
open TruthCore.Causality
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference

theorem actualSource_iff {World Being : Type} (m : Ontic World Being) (w : World)
    (x : Actual m w) : (actualGraph m w).Source x ↔
    ¬ ∃ y, m.ExistsAt w y ∧ m.Causes w y x.val := by
  sorry

theorem sourcePath_of_acc {Node : Type} (G : Graph Node) (x : Node)
    (hAcc : Acc G.edge x) : SourcePath G x := by
  sorry

theorem chain_injective {Node : Type} (G : Graph Node) (hNoCycles : G.NoCycles)
    (f : Nat → Node) (hStep : ∀ n, G.edge (f (n + 1)) (f n)) :
    Function.Injective f := by
  sorry

theorem source_or_regress {Node : Type} (G : Graph Node) (hNoCycles : G.NoCycles)
    (x : Node) : SourcePath G x ∨ AnchoredRegress G x := by
  sorry

theorem worldProjection {World Being : Type} (m : Ontic World Being)
    (hNoCycles : ActualAcyclic m) :
    {w | ∃ x, m.ExistsAt w x} = StarterWorlds m ∪ RegressWorlds m := by
  sorry

theorem finite_source {Node : Type} (G : Graph Node) [Finite Node]
    (hNoCycles : G.NoCycles) (x : Node) : ∃ s, G.Source s := by
  sorry

theorem checks {World Being : Type} (m : Ontic World Being)
    (hNoCycles : ActualAcyclic m) : WorldClassification m := by
  sorry

theorem overlapControl : OverlapControl := by
  sorry
end TruthCore.Results.Causality.WorldSourceRegress
