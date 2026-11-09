module

public import TruthCore.Causality.WorldSourceRegress

/-! Partial declaration completion for the shared A2/A10 entire-chain glossary.
The arbitrary carrier is the selected population, and `members` explicitly
selects a chain from it. No order, finiteness, linearity or actual-world policy
is imposed. Full cause and partial contribution are framework primitives;
neither implies the other by definition. Their applicability remains open.
This is NOT a declaration of the original composite sense: the interpretation
of its first-member clause awaits owner selection. -/

@[expose] public section

namespace TruthCore.Causality.EntireChainHead

/-- A selected chain population with two primitive production relations.
`cause y x` means y causes x; `partialCause y x` means y contributes partially
to causing x. These are productive relations, not mere temporal precedence,
explanatory relevance, grounding, capability or collective-whole production.
No transitivity, asymmetry, endpoint policy or well-foundedness is assumed. -/
structure Chain (Node : Type) where
  members : Node → Prop
  cause : Node → Node → Prop
  partialCause : Node → Node → Prop

/-- Full causes of selected members must themselves be selected members. -/
def Chain.Entire {Node : Type} (c : Chain Node) : Prop :=
  ∀ y x, c.members x → c.cause y x → c.members y

/-- Ungroundedness also excludes outside partial contributors to members.
The full-cause clause is retained even when the primitives are independent. -/
def Chain.Ungrounded {Node : Type} (c : Chain Node) : Prop :=
  c.Entire ∧ ∀ y x, c.members x → c.partialCause y x → c.members y

/-- An internal productive head contributes to a member and has no incoming
full OR partial cause from the chain. An isolated source is insufficient.
This predicate does not decide what the separate phrase 'first member' means. -/
def Chain.Head {Node : Type} (c : Chain Node) (h : Node) : Prop :=
  c.members h ∧
  (∃ x, c.members x ∧ (c.cause h x ∨ c.partialCause h x)) ∧
  ∀ y, c.members y → ¬ (c.cause y h ∨ c.partialCause y h)

/-- Closure plus an internal head excludes incoming causes from the entire
selected ambient carrier, without asserting any separate caused whole. -/
theorem head_uncaused {Node : Type} (c : Chain Node) (h : Node)
    (closed : c.Ungrounded) (head : c.Head h) :
    ∀ y, ¬ (c.cause y h ∨ c.partialCause y h) := by
  intro y incoming
  have member : c.members y := by
    cases incoming with
    | inl full => exact closed.1 y h head.1 full
    | inr contribution => exact closed.2 y h head.1 contribution
  exact head.2.2 y member incoming

namespace Controls

/-- An outside partial contributor is allowed by full closure alone. -/
def externalPartial : Chain Bool where
  members := fun x => x = true
  cause := fun _ _ => False
  partialCause := fun y x => y = false ∧ x = true

theorem full_closure_is_insufficient :
    externalPartial.Entire ∧ ¬ externalPartial.Ungrounded := by
  constructor
  · intro y x _ impossible
    exact False.elim impossible
  · intro h
    have bad := h.2 false true rfl ⟨rfl, rfl⟩
    cases bad

/-- A graph source with no outgoing production cannot be a head. -/
def isolated : Chain Unit where
  members := fun _ => True
  cause := fun _ _ => False
  partialCause := fun _ _ => False

theorem isolated_source_not_head :
    (TruthCore.Logic.Regress.Graph.mk isolated.cause).Source () ∧
    ¬ isolated.Head () := by
  constructor
  · rintro ⟨y, impossible⟩
    exact impossible
  · rintro ⟨_, ⟨x, _, productive⟩, _⟩
    exact productive.elim id id

/-- Branching production: the two incomparable sources both cause true.
No comparability or single predecessor is required for closure or heads. -/
def branching : Chain (Option Bool) where
  members := fun _ => True
  cause := fun y x => (y = none ∨ y = some false) ∧ x = some true
  partialCause := fun _ _ => False

theorem branching_heads :
    branching.Ungrounded ∧ branching.Head none ∧ branching.Head (some false) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro _ _ _ _; trivial
  · intro _ _ _ _; trivial
  · refine ⟨True.intro, ⟨some true, True.intro, Or.inl ⟨Or.inl rfl, rfl⟩⟩, ?_⟩
    intro y _ incoming
    rcases incoming with full | contribution
    · cases full.2
    · exact contribution
  · refine ⟨True.intro, ⟨some true, True.intro, Or.inl ⟨Or.inr rfl, rfl⟩⟩, ?_⟩
    intro y _ incoming
    rcases incoming with full | contribution
    · cases full.2
    · exact contribution

/-- Infinite upstream history is permitted; Nat here is only a control carrier,
not a restriction on Chain or a choice of the original first-member semantics. -/
def endless : Chain Nat where
  members := fun _ => True
  cause := fun y x => y = x + 1
  partialCause := fun _ _ => False

theorem endless_closed_with_incoming :
    endless.Ungrounded ∧ (∀ x, ∃ y, endless.cause y x) ∧
    (∀ x, ¬ endless.Head x) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro _ _ _ _; trivial
  · intro _ _ _ _; trivial
  · intro x; exact ⟨x + 1, rfl⟩
  · intro x h
    exact h.2.2 (x + 1) True.intro (Or.inl rfl)

end Controls
end TruthCore.Causality.EntireChainHead
