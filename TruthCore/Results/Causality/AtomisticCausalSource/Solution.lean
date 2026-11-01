import TruthCore.Causality.AtomisticCausalSource
import TruthCore.Logic.ExcludedMiddle

namespace TruthCore.Results.Causality.AtomisticCausalSource
open TruthCore.Logic.Regress (Graph)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Mereology.UniversalFusionBoundary (Composite Overlap Covers Fusion)
open TruthCore.Causality.AtomisticCausalSource

/-- Minimum source endpoint only, not effect-universality or necessity. -/
theorem source {B : Type} [PartialOrder B] (G : Graph B)
    (hPop : ObjectPopulation B) (hAtomic : AtomicParts B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hEM : ExcludedMiddle) : SourceExists G := by
  rcases hEM (SourceExists G) with hSource | hNone
  · exact hSource
  · have allCaused : ∀ x, ∃ c, G.edge c x := by
      intro x
      rcases hEM (∃ c, G.edge c x) with hCause | hNoCause
      · exact hCause
      · exact (hNone ⟨x, hNoCause⟩).elim
    obtain ⟨x⟩ := hPop
    obtain ⟨a, _, ha⟩ := hAtomic x
    have hNonempty : (CausedSimples G).Nonempty := ⟨a, ha, allCaused a⟩
    obtain ⟨whole, hParts⟩ := hCover hNonempty
    obtain ⟨c, hc⟩ := allCaused whole
    obtain ⟨p, hpc, hp⟩ := hAtomic c
    have hpw := hParts p ⟨hp, allCaused p⟩
    exact (hNoOverlap c whole hc ⟨p, hpc, hpw⟩).elim

/-- Activity gives the SAME selected source an outgoing effect. -/
theorem outgoing {B : Type} [PartialOrder B] (G : Graph B)
    (hPop : ObjectPopulation B) (hAtomic : AtomicParts B)
    (hCover : ConditionalCausedSimpleCover G) (hNoOverlap : CauseEffectNonoverlap G)
    (hEM : ExcludedMiddle) (hActivity : CausalActivity G) : OutgoingSourceExists G := by
  obtain ⟨x, hx⟩ := source G hPop hAtomic hCover hNoOverlap hEM
  rcases hActivity x with hi | ho
  · exact (hx hi).elim
  · exact ⟨x, hx, ho⟩

/-- Finite, nonvacuous consistency of the nonlogical interfaces and activity. -/
theorem consistency : Consistency := by
  have hSimple : ∀ x : Fixture.Object, IsMin x := by
    intro x p hp
    exact hp.symm
  have hFamily : CausedSimples Fixture.graph = {Fixture.Object.effect} := by
    apply Set.ext
    intro a
    constructor
    · rintro ⟨_, c, hc⟩
      exact Set.mem_singleton_iff.mpr hc.2
    · intro ha
      have heq := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨hSimple _, Fixture.Object.origin, rfl, rfl⟩
  have hNoComposite : ∀ x : Fixture.Object, ¬ Composite x := by
    intro x ⟨p, hp⟩
    exact hp.not_ge (hSimple x hp.le)
  have hRoot : Fixture.graph.Source Fixture.Object.origin := by
    rintro ⟨c, hc⟩
    cases hc.2
  have hOut : OutgoingSourceExists Fixture.graph :=
    ⟨.origin, hRoot, .effect, (by intro h; cases h), rfl, rfl⟩
  refine ⟨⟨.origin⟩, ?_, ?_, ?_, ?_, ?_, ?_, hSimple, hFamily, ?_, ?_, hOut⟩
  · intro x
    exact ⟨x, rfl, hSimple x⟩
  · intro _
    refine ⟨.effect, ?_⟩
    rintro a ⟨_, c, hc⟩
    exact hc.2
  · intro c e hc ⟨p, hpc, hpe⟩
    change p = c at hpc
    change p = e at hpe
    have hce := hpc.symm.trans hpe
    have hBad := hc.1.symm.trans (hce.trans hc.2)
    cases hBad
  · intro x
    cases x with
    | origin => exact Or.inr ⟨.effect, (by intro h; cases h), rfl, rfl⟩
    | effect => exact Or.inl ⟨.origin, rfl, rfl⟩
  · intro e c d hc hd
    exact hc.1.trans hd.1.symm
  · intro x _ hx
    exact (hNoComposite x hx).elim
  · constructor
    · rintro a ⟨_, c, hc⟩
      exact hc.2
    · intro p hp
      refine ⟨.effect, ⟨hSimple _, .origin, rfl, rfl⟩, ?_⟩
      exact ⟨p, le_refl p, hp⟩
  · exact ⟨.origin, hRoot⟩

end TruthCore.Results.Causality.AtomisticCausalSource
