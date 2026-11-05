module
public import TruthCore.Causality.CommonPriority
@[expose] public section
namespace TruthCore.Results.Causality.CommonPriority
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.CommonPriority
open TruthCore.German.Kant.CosmologicalInference
namespace M
export TruthCore.Models.NecessarilyUnderived (rotating rotatingSupport varying varyingSupport)
end M

theorem rank_to_union {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h : CommonRank m R a) : WellFoundedUnionNecessarySupport m R a := by
  obtain ⟨Rank, priority, hWF, rank, hPreserves⟩ := h
  let f : TruthCore.Logic.Regress.Graph.Map
      ⟨UnionNecessarySupport m R a⟩ ⟨priority⟩ :=
    ⟨rank, fun {g n} h => hPreserves g n h⟩
  exact f.wellFounded hWF

theorem union_to_rank {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h : WellFoundedUnionNecessarySupport m R a) : CommonRank m R a := by
  exact ⟨B, UnionNecessarySupport m R a, h, id, fun _ _ h => h⟩

theorem from_rank {W B : Type} (m : Ontic W B) (R : W → B → B → Prop) (a : W)
    (h0 : NecessaryBeing m a) (h1 : ActualReflexive m a)
    (h2 : NoContingentGroundOfNecessary m R a) (h3 : CommonRank m R a)
    (h4 : TruthCore.Logic.ExcludedMiddle) : NecessarilyUnderived m R a := by
  exact TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
    m R a h0 h1 h2 (rank_to_union m R a h3) h4

private theorem stable_noNovel {W B : Type} (m : Ontic W B) R a
    (hRef : ActualReflexive m a) (h : NecessarySupportStable m R a) :
    NoNovelNecessarySupport m R a := by
  intro w g n hg hn he hr
  exact h w a g n hg hn he hr (hg a hRef) (hn a hRef)

theorem comparison : Comparison := by
  refine ⟨?_, TruthCore.Models.NecessarilyUnderived.rotatingWorldWellFounded,
    ?_, TruthCore.Models.NecessarilyUnderived.rotatingNecessary,
    TruthCore.Models.NecessarilyUnderived.rotatingReflexive,
    TruthCore.Models.NecessarilyUnderived.rotatingNoContingentGround, ?_,
    TruthCore.Models.NecessarilyUnderived.rotatingNoUnderived,
    TruthCore.Results.Causality.ParityUnionRegress.checks, ?_, ?_, ?_, ?_⟩
  · intro W B m R a hRef hStable hWF
    exact union_to_rank m R a (union_wellFounded_of_actual_wellFounded m R a
      hRef (stable_noNovel m R a hRef hStable) hWF)
  · intro _ _ _ _ _ _ _ _
    trivial
  · intro h
    exact TruthCore.Models.NecessarilyUnderived.rotatingUnionNotWellFounded
      (rank_to_union _ _ _ h)
  · intro _ _ _ _ _ _ _ _
    trivial
  · intro h
    exact TruthCore.Results.Causality.ParityUnionRegress.unionNotWF
      (rank_to_union _ _ _ h)
  · exact union_to_rank _ _ _ TruthCore.Models.NecessarilyUnderived.varyingUnionWellFounded
  · intro h
    exact TruthCore.Models.NecessarilyUnderived.varyingNoNovelSupport
      (stable_noNovel _ _ _ TruthCore.Models.NecessarilyUnderived.varyingReflexive h)
end TruthCore.Results.Causality.CommonPriority
