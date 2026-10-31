import TruthCore.Causality.ContingentAncestry

/-! A strictness interpretation: a contingent target is grounded in two
necessary beings that support each other. Necessary existence is witnessed,
while an actual root and full-cone well-foundedness fail. No metaphysical
possibility or adequacy of the necessary cycle is asserted. -/
namespace TruthCore.Models.ContingentAncestry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.SelectedAncestry
open TruthCore.Causality.ContingentAncestry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

inductive Node where
  | left | right | target
  deriving DecidableEq

def model : Profile Bool Node where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt w x := x = .left ∨ x = .right ∨ w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds w source downstream := w = false ∧
    ((source = .left ∧ downstream = .right) ∨
     (source = .right ∧ downstream = .left) ∨
     (source = .left ∧ downstream = .target))

private theorem contingentOnlyTarget (x : Node)
    (h : ContingentAt model.ontic false x) : x = .target := by
  cases x with
  | left =>
    obtain ⟨_, v, _, hv⟩ := h
    exact False.elim (hv (Or.inl rfl))
  | right =>
    obtain ⟨_, v, _, hv⟩ := h
    exact False.elim (hv (Or.inr (Or.inl rfl)))
  | target => rfl

private theorem noTargetSource (downstream : Node) :
    ¬ model.grounds false .target downstream := by
  rintro ⟨_, ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩⟩ <;> cases h

private theorem leftCone : Cone model false .target .left := by
  refine ⟨⟨trivial, Or.inl rfl⟩, ?_⟩
  exact Relation.ReflTransGen.single
    ⟨trivial, Or.inl rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

private theorem rightCone : Cone model false .target .right := by
  refine ⟨⟨trivial, Or.inr (Or.inl rfl)⟩, ?_⟩
  exact Relation.ReflTransGen.head
    ⟨trivial, Or.inr (Or.inl rfl), rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩ leftCone.2

/-- Retains an actually contingent selected target and local dependence;
contingent-only foundation holds, full-cone foundation fails. A necessary
ancestor exists, but no actual grounding root ancestor exists. -/
def Strictness : Prop :=
  ActualConcrete model false .target ∧ ContingentAt model.ontic false .target ∧
  ConeContingentGrounded model false .target ∧
  ContingentConeFounded model false .target ∧
  ¬ ConeWellFounded model false .target ∧
  NecessaryAncestor model false .target ∧
  ¬ NecessaryRootAncestor model false .target

theorem strictness : Strictness := by
  refine ⟨⟨trivial, Or.inr (Or.inr rfl)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Or.inr (Or.inr rfl), true, trivial, ?_⟩
    rintro (h | h | h) <;> cases h
  · intro x _ hContingent
    have hx := contingentOnlyTarget x hContingent
    exact ⟨.left, trivial, Or.inl rfl, rfl, Or.inr (Or.inr ⟨rfl, hx⟩)⟩
  · constructor
    intro fact
    cases fact with
    | fact downstream =>
      apply Acc.intro
      intro reason hReason
      cases reason with
      | fact source =>
        have hSource := contingentOnlyTarget source hReason.2.2.2.1
        exact False.elim (noTargetSource downstream
          ((congrArg (fun x => model.grounds false x downstream) hSource).mp
            hReason.2.2.1.2.2.2))
  · intro hWF
    let leftNode : {x // Cone model false .target x} := ⟨.left, leftCone⟩
    let rightNode : {x // Cone model false .target x} := ⟨.right, rightCone⟩
    have walk : ∀ x : {x // Cone model false .target x},
        x.val = .left ∨ x.val = .right → False := by
      intro x
      induction x using hWF.induction with
      | h x ih =>
        intro hRole
        rcases hRole with hLeft | hRight
        · apply ih rightNode
          · exact (congrArg (fun t => model.grounds false rightNode.val t) hLeft).mpr
              ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          · exact Or.inr rfl
        · apply ih leftNode
          · exact (congrArg (fun t => model.grounds false leftNode.val t) hRight).mpr
              ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inl rfl
    exact walk leftNode (Or.inl rfl)
  · exact ⟨.left, leftCone, fun _ _ => Or.inl rfl⟩
  · rintro ⟨x, _, _, hRoot⟩
    cases x with
    | left =>
      exact hRoot .right
        ⟨trivial, Or.inr (Or.inl rfl), rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | right => exact hRoot .left ⟨trivial, Or.inl rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | target =>
      exact hRoot .left
        ⟨trivial, Or.inl rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

end TruthCore.Models.ContingentAncestry
