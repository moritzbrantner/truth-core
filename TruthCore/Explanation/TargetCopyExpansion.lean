import TruthCore.Causality.BruteFoundationExplanations
import TruthCore.Explanation.ExistencePSR
import TruthCore.Causality.LocalTransmission
import TruthCore.Logic.Regress

/-! A failed discriminator for #698. Modal entailment is not enough when the
reason's truth is freely copied from the target. These are mathematical
expansions, not independently adequate existence explanations. -/
namespace TruthCore.Explanation.TargetCopyExpansion
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.BruteFoundationExplanations
open TruthCore.Explanation.ExistencePSR
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic.Regress

/-- Keep the entire old reality, including its concrete/grounds assignments.
The reason sort uses existing existence-fact tags, not new ontic beings.
Its truth literally repeats the concrete target's existence. -/
def copied (m : Profile W B) : ExplanationProfile W B (ExistenceFact B) where
  reality := m
  reasonPresent := fun w r => match r with
    | .fact x => m.concrete x ∧ m.ontic.ExistsAt w x
  explains := fun w r x => r = .fact x ∧ m.concrete x ∧ m.ontic.ExistsAt w x

/-- The already existing modal-sufficiency test is imposed on every admitted
link, in addition to soundness and coverage. No explanatory direction,
independent real nature or anti-circularity requirement is hidden here. -/
def EntailingCoverage (m : ExplanationProfile W B R) : Prop :=
  ExplanationSound m ∧ LocallyExplained m ∧
    ∀ w r x, m.explains w r x → NecessitatesExistenceAt m w r x

/-- One common inhabited arena: two complete alternative worlds, rigid Nat
candidates, all present and concrete at both worlds, universal accessibility.
The supplied graph interprets BOTH modeled Causes and grounds in this test;
this assignment is not a general identity of causal and grounding relations. -/
def arena (g : Graph Nat) : Profile Bool Nat where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ => g.edge
  }
  concrete := fun _ => True
  grounds := fun _ => g.edge

def single : Graph Nat := ⟨fun y x => y = 0 ∧ x ≠ 0⟩
def plural : Graph Nat := ⟨fun y x => y ≤ 1 ∧ 2 ≤ x⟩
def descending : Graph Nat := ⟨fun y x => y = x + 1⟩

/-- Same population, worlds, identity and interpretation policy; only the
specified dependence graph varies. These are relation-relative sources, not
God, independent intrinsic natures or sufficient totality explanations. -/
def ArenaControls : Prop :=
  (∀ (g : Graph Nat) w, InhabitedAt (arena g) w ∧
    ∀ n, NecessaryAt (arena g).ontic w n) ∧
  (∃! n, single.Source n) ∧
  plural.Source 0 ∧ plural.Source 1 ∧
  (∀ n, plural.Source n → n = 0 ∨ n = 1) ∧
  (∀ n, ¬ descending.Source n) ∧ ¬ WellFounded descending.edge ∧
  (∀ g, EntailingCoverage (copied (arena g))) ∧
  (∀ g, ¬ ∃ r, ∀ x, (copied (arena g)).explains false r x)

/-- Universal model expansion plus validity conservativity and common-arena
controls. A property solely of the ORIGINAL reality is restricted by none of
these freely target-coded entailing expansions. The final conjunct denies one
common memberwise token, not an explanation of a newly reified whole. -/
def Certificate : Prop :=
  (∀ (W B : Type) (m : Profile W B),
    (copied m).reality = m ∧ EntailingCoverage (copied m)) ∧
  (∀ (W B : Type) (P : Profile W B → Prop),
    (∀ e : ExplanationProfile W B (ExistenceFact B), EntailingCoverage e → P e.reality) ↔
      ∀ m, P m) ∧ ArenaControls

end TruthCore.Explanation.TargetCopyExpansion
