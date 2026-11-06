module

public import TruthCore.Causality.MaximalGroundingAsymmetry

@[expose] public section
namespace TruthCore.Results.Causality.MaximalGroundingAsymmetry.Control
open TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- Analyst same-dictionary scope consequence; all original source/Challenge interfaces preserved. -/
theorem populatedStrictness : PopulatedStrictness := by
  open Control Control.Node in
  have hMax : IsMaximumIn act more () root := ⟨trivial, fun y h => by cases h.2 rfl⟩
  have hOnly : ∀ x, IsMaximumIn act more () x → x = root := by
    intro x hx
    cases x with
    | root => rfl
    | left => exact False.elim (hx.2 root ⟨rfl, by decide⟩)
    | right => exact False.elim (hx.2 root ⟨rfl, by decide⟩)
  have hNoIncoming : ∀ y, ¬ grounds y root := by
    intro y h
    rcases h with ⟨_, hn⟩ | ⟨_, he⟩ | ⟨_, he⟩
    · exact hn rfl
    · exact Node.noConfusion he
    · exact Node.noConfusion he
  have hRoot : ActualRoot model () root := by
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    intro y hy
    exact hNoIncoming y hy.2.2
  refine ⟨⟨root, trivial, trivial⟩, (fun _ _ => trivial), ?_, ?_, ?_, ?_,
    hRoot, hMax, ⟨trivial,trivial⟩, ⟨trivial,trivial⟩, by decide, ?_, ?_,
    Or.inr (Or.inl ⟨rfl,rfl⟩), Or.inr (Or.inr ⟨rfl,rfl⟩), ?_⟩
  · intro c x _ _ hc
    exact ⟨trivial,trivial,Or.inl hc⟩
  · intro c hc x hx _
    have heq := hOnly c hc
    subst c
    exact ⟨rfl,hx⟩
  · intro _
    exact ⟨root,hMax⟩
  · intro a b _ _ hb hab _
    have hEq := hOnly b hb
    subst b
    exact hNoIncoming a hab
  · intro h
    exact Control.Node.noConfusion (hOnly left h)
  · intro h
    exact Control.Node.noConfusion (hOnly right h)
  · intro h
    exact h left right ⟨trivial,trivial⟩ ⟨trivial,trivial⟩
      (Or.inr (Or.inl ⟨rfl,rfl⟩)) (Or.inr (Or.inr ⟨rfl,rfl⟩))

end TruthCore.Results.Causality.MaximalGroundingAsymmetry.Control
