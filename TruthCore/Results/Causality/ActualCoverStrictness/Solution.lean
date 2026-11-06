module

public import TruthCore.Causality.ActualCoverStrictness
public import TruthCore.Results.Causality.ActualCoverNecessaryBeing.Solution

@[expose] public section
namespace TruthCore.Results.Causality.ActualCoverStrictness
open TruthCore.Causality.ActualCoverStrictness
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.ActualFusionNecessaryBeing
open TruthCore.Causality.ActualCoverNecessaryBeing
open TruthCore.Mereology.UniversalFusionBoundary (Overlap)
open TruthCore.Mereology.FusionNoNecessaryParts
open TruthCore.German.Kant.CosmologicalInference

private theorem le_iff (a b : Body) : a ≤ b ↔ a = b ∨ a = .shared := Iff.rfl

private theorem sourceNecessary : NecessaryAt model.ontic false .source :=
  fun _ _ => Or.inl rfl

private theorem necessary_eq (p : Body) (h : NecessaryAt model.ontic false p) :
    p = .source := by
  have ht := h true True.intro
  change p = .source ∨ true = false at ht
  rcases ht with hp | hf
  · exact hp
  · cases hf

private theorem noParts (x : Body) (hx : x ≠ .source) :
    NoNecessaryPartsAt model.ontic false x := by
  intro p hp hn
  have heq := necessary_eq p hn
  subst p
  rcases (le_iff .source x).mp hp with h | h
  · exact hx h.symm
  · cases h

theorem checks : Certificate := by
  have pop : TruthCore.Explanation.WellFoundedSource.PopulatedAt model false :=
    ⟨.effect, Or.inr rfl⟩
  have hfEffect : ActualNoNecessaryPartsFamily model.ontic false .effect :=
    ⟨Or.inr rfl, noParts .effect (by intro h; cases h)⟩
  have hfShared : ActualNoNecessaryPartsFamily model.ontic false .shared :=
    ⟨Or.inr rfl, noParts .shared (by intro h; cases h)⟩
  have cover : ActualCoverAt model.ontic false .effect := by
    refine ⟨Or.inr rfl, ?_⟩
    intro x hx
    cases x with
    | shared => exact Or.inr rfl
    | effect => exact le_refl _
    | source => exact False.elim (hx.2 .source (le_refl _) sourceNecessary)
  have conditional : ConditionalActualCoverAt model.ontic false :=
    fun _ => ⟨.effect, cover⟩
  have href : TruthCore.Causality.NecessarilyUnderived.ActualReflexive model.ontic false :=
    True.intro
  have causal : ActualNoNecessaryPartsHaveCausesAt model.ontic false := by
    intro x _ hn
    refine ⟨.source, rfl, ?_, rfl⟩
    intro heq
    subst x
    exact hn .source (le_refl _) sourceNecessary
  have endpoints : CausesHaveActualEndpointsAt model.ontic false := by
    intro _ _ _
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  have nonpart : CauseNotPartOfEffectAt model.ontic false := by
    intro c e hc hp
    rcases hc with ⟨rfl, hne, _⟩
    rcases (le_iff .source e).mp hp with h | h
    · exact hne h.symm
    · cases h
  have sourceEffect : model.ontic.Causes false .source .effect :=
    ⟨rfl, (by intro h; cases h), rfl⟩
  have sourceShared : model.ontic.Causes false .source .shared :=
    ⟨rfl, (by intro h; cases h), rfl⟩
  have overlap : Overlap (.source : Body) .effect :=
    ⟨.shared, Or.inr rfl, Or.inr rfl⟩
  have noSourcePart : ¬ (.source : Body) ≤ .effect := fun h => nonpart _ _ sourceEffect h
  have noEffectPart : ¬ (.effect : Body) ≤ .source := by
    intro h
    rcases (le_iff .effect .source).mp h with h | h <;> cases h
  have nonoverlapFails : ¬ CauseEffectNonoverlapAt model.ontic false :=
    fun h => h .source .effect sourceEffect overlap
  have intended : ∃ p : TruthCore.Causality.CausalPowerConcreteness.IntendedProfile Bool Body,
      p.underlying = profile ∧ (∀ x, ¬ p.abstract x) ∧
      (∀ w x, p.hasCausalPower w x ↔ x = .source) := by
    refine ⟨{
      underlying := profile
      abstract := fun _ => False  -- category-constant: intended (no abstract candidate; meets the #1094 contract but supplies no Anchors, so not an intended interpretation under #1103)
      hasCausalPower := fun _ x => x = .source
      disjoint := fun _ h => h.elim
      powerExists := fun _ _ h => Or.inl h
      causalEndpoints := ?_
      exerciseHasPower := fun _ _ _ h => h.1
      powerConcrete := fun _ _ _ => True.intro }, rfl, ?_, ?_⟩
    · intro w c e h
      exact ⟨Or.inl h.1, Or.inr h.2.2⟩
    · exact fun _ h => h.elim
    · exact fun _ _ => Iff.rfl
  have ne := TruthCore.Results.Causality.ActualCoverNecessaryBeing.fromPopulation
    model false pop conditional href causal endpoints nonpart
  exact ⟨pop, conditional, href, causal, endpoints, nonpart, sourceEffect,
    sourceShared, hfEffect, hfShared, cover, Or.inr rfl, Or.inr rfl,
    (by intro h; cases h), (by intro h; cases h), noSourcePart,
    noEffectPart, overlap, nonoverlapFails, intended, ne⟩

end TruthCore.Results.Causality.ActualCoverStrictness
