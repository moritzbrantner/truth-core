import TruthCore.Causality.SelectedAncestry

/-! Same-semantics controls for the one-complete-cone theorem. These are formal
interpretations, not metaphysical possibilities or adequate rivals retaining
the omitted premise. -/
namespace TruthCore.Models.SelectedAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.SelectedAncestry
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)

/-- One contingent ungrounded actual candidate. -/
def brute : Profile Bool Unit where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun _ _ _ => False

/-- One source-free successor chain of actual contingent candidates. -/
def chain : Profile Bool Nat where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun w source downstream => w = false ∧ source = downstream + 1

inductive Node where
  | root | target | chain (n : Nat) | brute
  deriving DecidableEq

/-- The selected contingent target has the necessary root as its whole proper
ancestry. A disjoint infinite chain and brute singleton are also actual. -/
def combined : Profile Bool Node where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x = .root ∨ w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun w source downstream => w = false ∧
    ((source = .root ∧ downstream = .target) ∨
      ∃ n, source = .chain (n + 1) ∧ downstream = .chain n)

private theorem noParentRoot (source : Node) : ¬ combined.grounds false source .root := by
  rintro ⟨_, ⟨_, h⟩ | ⟨_, _, h⟩⟩ <;> cases h

private theorem parentOfTarget (source : Node)
    (h : combined.grounds false source .target) : source = .root := by
  rcases h with ⟨_, ⟨hs, _⟩ | ⟨_, _, h⟩⟩
  · exact hs
  · cases h

private theorem coneOnly {x : Node} (h : GroundAncestor combined false x .target) :
    x = .root ∨ x = .target := by
  refine Relation.ReflTransGen.head_induction_on h (Or.inr rfl) ?_
  intro source downstream hEdge _ ih
  rcases ih with hRoot | hTarget
  · exact False.elim (noParentRoot source (hRoot ▸ hEdge.2.2))
  · exact Or.inl (parentOfTarget source (hTarget ▸ hEdge.2.2))

/-- Each omission retains the selected actual being and the other local
premise, but no necessary concrete being exists. The combined interpretation
retains an actually contingent selected target and both local premises while
both global premises fail; the unrelated chain is genuinely infinite. -/
def Controls : Prop :=
  (ActualConcrete brute false () ∧ ConeWellFounded brute false () ∧
    ¬ ConeContingentGrounded brute false () ∧ ¬ NecessaryConcreteAt brute false) ∧
  (ActualConcrete chain false 0 ∧ ConeContingentGrounded chain false 0 ∧
    ¬ ConeWellFounded chain false 0 ∧ ¬ NecessaryConcreteAt chain false) ∧
  (ActualConcrete combined false .target ∧ ContingentAt combined.ontic false .target ∧
    ConeWellFounded combined false .target ∧ ConeContingentGrounded combined false .target ∧
    NecessaryRootAncestor combined false .target ∧
    ¬ ActualGroundingWF combined false ∧ ¬ EveryContingentGroundedAt combined false ∧
    (∀ n, ActualConcrete combined false (.chain n) ∧
      combined.grounds false (.chain (n + 1)) (.chain n)))

theorem controls : Controls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨trivial, rfl⟩, ?_, ?_, ?_⟩
    · constructor
      intro x
      apply Acc.intro
      intro y hEdge
      exact False.elim hEdge
    · intro hDep
      obtain ⟨_, hGround⟩ := hDep () ⟨⟨trivial, rfl⟩, .refl⟩
        ⟨rfl, true, trivial, Bool.noConfusion⟩
      exact hGround.2.2
    · rintro ⟨_, _, _, hNecessary⟩
      exact Bool.noConfusion (hNecessary true trivial)
  · refine ⟨⟨trivial, rfl⟩, ?_, ?_, ?_⟩
    · intro x _ _
      exact ⟨x + 1, trivial, rfl, rfl, rfl⟩
    · intro hWF
      have walk : ∀ a : {x // Cone chain false 0 x},
          Acc (fun a b : {x // Cone chain false 0 x} => chain.grounds false a.val b.val) a → False := by
        intro a ha
        induction ha with
        | intro a _ ih =>
          exact ih ⟨a.val + 1, ⟨trivial, rfl⟩,
            Relation.ReflTransGen.head ⟨trivial, rfl, rfl, rfl⟩ a.property.2⟩ ⟨rfl, rfl⟩
      exact walk ⟨0, ⟨trivial, rfl⟩, .refl⟩ (hWF.apply _)
    · rintro ⟨_, _, _, hNecessary⟩
      exact Bool.noConfusion (hNecessary true trivial)
  · refine ⟨⟨trivial, Or.inr rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨Or.inr rfl, true, trivial, ?_⟩
      rintro (h | h) <;> cases h
    · constructor
      intro candidate
      apply Acc.intro
      intro source hEdge
      rcases coneOnly candidate.property.2 with hRoot | hTarget
      · exact False.elim (noParentRoot source.val (hRoot ▸ hEdge))
      · have hSource := parentOfTarget source.val
          ((congrArg (fun t : Node => combined.grounds false source.val t) hTarget).mp hEdge)
        apply Acc.intro
        intro parent hParent
        exact False.elim (noParentRoot parent.val (hSource ▸ hParent))
    · intro x hCone hCont
      rcases coneOnly hCone.2 with hRoot | hTarget
      · obtain ⟨_, v, _, hv⟩ := hCont
        exact False.elim (hv (Or.inl hRoot))
      · exact ⟨.root, trivial, Or.inl rfl, rfl, Or.inl ⟨rfl, hTarget⟩⟩
    · refine ⟨.root, ⟨⟨trivial, Or.inl rfl⟩, ?_⟩, ?_, ?_⟩
      · exact Relation.ReflTransGen.single ⟨trivial, Or.inl rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · intro _ _
        exact Or.inl rfl
      · intro source hEdge
        exact noParentRoot source hEdge.2.2
    · apply not_wf_of_descent combined false (fun x => ∃ n, x = .chain n)
        (fun _ _ => ⟨trivial, Or.inr rfl⟩) ?_ (.chain 0) ⟨0, rfl⟩
      rintro x ⟨n, rfl⟩
      exact ⟨.chain (n + 1), ⟨n + 1, rfl⟩, rfl, Or.inr ⟨n, rfl, rfl⟩⟩
    · intro hDep
      obtain ⟨source, _, _, hGround⟩ := hDep .brute trivial (Or.inr rfl)
        ⟨Or.inr rfl, true, trivial, (by rintro (h | h) <;> cases h)⟩
      rcases hGround with ⟨_, ⟨_, h⟩ | ⟨_, _, h⟩⟩ <;> cases h
    · intro n
      exact ⟨⟨trivial, Or.inr rfl⟩, rfl, Or.inr ⟨n, rfl, rfl⟩⟩

end TruthCore.Models.SelectedAncestry
