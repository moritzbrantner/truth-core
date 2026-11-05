import TruthCore.Causality.CommonPriority
namespace TruthCore.Results.Causality.CommonPriority
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.CommonPriority
open TruthCore.German.Kant.CosmologicalInference

theorem rank_to_union {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h : CommonRank m R a) : WellFoundedUnionNecessarySupport m R a := by sorry

theorem union_to_rank {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h : WellFoundedUnionNecessarySupport m R a) : CommonRank m R a := by sorry

theorem from_rank {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h0 : NecessaryBeing m a) (h1 : ActualReflexive m a)
    (h2 : NoContingentGroundOfNecessary m R a) (h3 : CommonRank m R a)
    (h4 : TruthCore.Logic.ExcludedMiddle) : NecessarilyUnderived m R a := by sorry

theorem comparison : Comparison := by sorry
end TruthCore.Results.Causality.CommonPriority
