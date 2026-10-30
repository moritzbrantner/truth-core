import TruthCore.Logic.Strength.Cause
namespace TruthCore.Results.Logic.StrengthCause
open TruthCore.Logic.Strength.Cause TruthCore.Greek.Plato.Timaeus
universe u

theorem implication {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hS : DistinctCausePrinciple G C) : CausePrinciple G C := by
  intro x hx
  obtain ⟨y, _, hy⟩ := hS x hx
  exact ⟨y, hy⟩

theorem deltaForward {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hS : DistinctCausePrinciple G C) :
    SelfCausingGeneratedHaveAlternativeCause G C := by
  intro x hx _
  exact hS x hx

theorem reconstruction {Entity : Type u} [DecidableEq Entity] (G : Entity → Prop)
    (C : Entity → Entity → Prop) (hW : CausePrinciple G C)
    (hD : SelfCausingGeneratedHaveAlternativeCause G C) : DistinctCausePrinciple G C := by
  intro x hx
  obtain ⟨y, hy⟩ := hW x hx
  by_cases same : y = x
  · exact hD x hx (same ▸ hy)
  · exact ⟨y, same, hy⟩

theorem equivalence : ExactDelta := by
  intro Entity _ G C
  exact ⟨fun h => ⟨implication G C h, deltaForward G C h⟩,
    fun h => reconstruction G C h.1 h.2⟩

theorem separator : SelfOnlySeparates := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro x _
    exact ⟨x, rfl⟩
  · intro h
    obtain ⟨y, ne, hy⟩ := h false rfl
    exact ne hy

theorem mixedControl : MixedSelfAndOtherAllowed := by
  constructor
  · intro x _ _
    cases x
    · exact ⟨true, Bool.noConfusion, True.intro⟩
    · exact ⟨false, Bool.noConfusion, True.intro⟩
  · exact True.intro

theorem noCauseControl : NoCauseDeltaControl := by
  constructor
  · intro _ _ h
    exact False.elim h
  · intro h
    obtain ⟨_, impossible⟩ := h false True.intro
    exact impossible
theorem nonRestatementControl : DeltaNotConditionalRestatement := by
  constructor
  · intro hW
    obtain ⟨_, _, impossible⟩ := hW true True.intro
    exact False.elim (Bool.noConfusion impossible)
  · intro hD
    obtain ⟨y, ne, hy, _⟩ := hD false True.intro ⟨rfl, rfl⟩
    exact ne hy
end TruthCore.Results.Logic.StrengthCause
