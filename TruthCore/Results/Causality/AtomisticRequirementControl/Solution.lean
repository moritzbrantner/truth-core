module

public import TruthCore.Causality.AtomisticRequirementControl
public import TruthCore.Results.Causality.AtomisticUniversalCausePriority.Solution

@[expose] public section
namespace TruthCore.Results.Causality.AtomisticRequirementControl
open TruthCore.Causality.AtomisticRequirementControl
open TruthCore.Causality.AtomisticCausalSource
open TruthCore.Causality.AtomisticUniversalCausePriority
open TruthCore.Causality.CompleteCauseContributorCover
open TruthCore.Mereology.UniversalFusionBoundary
open TruthCore.Mereology.SupplementationFusion

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem certificate : Certificate := by
  have hWF : ProperPartWF Object := by
    have hRank : ∀ x y : Object, x < y → rank x < rank y := by decide
    exact Subrelation.wf (fun {x y} h => hRank x y h) (measure rank).wf
  have hCover : ConditionalCausedSimpleCover graph := by
    intro _
    refine ⟨Object.m, ?_⟩
    change ∀ x : Object, (IsMin x ∧ ∃ c, graph.edge c x) → x ≤ Object.m
    unfold IsMin
    decide
  have hUniversal : UniversalCausePriority graph prior := by
    exact TruthCore.Results.Causality.AtomisticUniversalCausePriority.universalPriority
      graph prior (by exact ⟨Object.r⟩) hWF
      hCover
      (by unfold CauseEffectNonoverlap Overlap; decide)
      (by unfold CausalActivity; decide)
      (by intro P; exact Classical.em P)
      (by unfold CausedCompositeHasCausedProperPart Composite; decide)
      (by unfold CausePriorToEffectParts; decide)
      (by unfold ProperPartsPrior; decide)
      (by unfold TransitiveExistentialPriority; decide)
  unfold Certificate
  refine ⟨Classical.em, ⟨Object.r⟩, ?_, hWF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hUniversal, ?_, ?_, ?_, ?_, ?_⟩
  · unfold AtomicParts IsMin; decide
  · unfold CausalActivity; decide
  · exact hCover
  · unfold CauseEffectNonoverlap Overlap; decide
  · unfold CausedCompositeHasCausedProperPart Composite; decide
  · unfold UniqueCausePerEffect; decide
  · unfold CausePriorToEffectParts; decide
  · unfold ProperPartsPrior; decide
  · unfold TransitiveExistentialPriority; decide
  · unfold WeakSupplementation Overlap; decide
  · unfold ProducerParticipates; decide
  · unfold CompleteCauseCoversContributors Covers
    change ∀ c e : Object, graph.edge c e → ∀ x : Object, x ∈ participants e → x ≤ c
    decide
  · unfold Fusion Overlap IsMin; decide
  · ext a
    change (IsMin a ∧ ∃ c, graph.edge c a) ↔ (a = .p ∨ a = .q)
    unfold IsMin
    revert a
    decide
  · unfold Fusion CausedSimples Overlap IsMin; decide
  · decide
  · unfold Composite; decide
  · decide
  · unfold Composite; decide
  · decide
  · decide
  · decide
  · unfold TruthCore.Logic.Regress.Graph.Source; decide
  · decide
  · decide
  · decide
  · decide

end TruthCore.Results.Causality.AtomisticRequirementControl
