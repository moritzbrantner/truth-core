module

public import TruthCore.Causality.WorldSourceRegress

/-! Partial declaration completion for the shared A2/A10 entire-chain glossary.
The arbitrary carrier is the selected population, and `members` explicitly
selects a chain from it. No order, finiteness, linearity or actual-world policy
is imposed. Full cause and partial contribution are framework primitives;
neither implies the other by definition. Their applicability remains open.
This is NOT a declaration of the original composite sense: the interpretation
of its first-member clause remains unmapped; approved sibling profiles follow. -/

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

/-- Causal incoming-minimum reading. Both full and partial causes count;
self-causation counts as incoming. No positive predecessor choice is asserted. -/
structure CausalNoFirst {Node : Type} (c : Chain Node) : Prop where
  noMinimum : ¬ ∃ x, c.members x ∧
    ∀ y, c.members y → ¬ (c.cause y x ∨ c.partialCause y x)

/-- A separately supplied strict order profile on the SAME carrier.
Irreflexivity and transitivity are explicit guards, not causal laws.
Nonlinearity is permitted. Applicability and cause/order alignment are open. -/
structure OrderedChain (Node : Type) where
  chain : Chain Node
  before : Node → Node → Prop
  strictOrder : IsStrictOrder Node before

/-- No minimal selected member in the separate order; not merely no least. -/
structure OrderedNoFirst {Node : Type} (o : OrderedChain Node) : Prop where
  noMinimum : ¬ ∃ x, o.chain.members x ∧
    ∀ y, o.chain.members y → ¬ o.before y x

/-- A least member must precede every distinct member; incomparable minima
need not be least. Equality is explicit, so the order stays strict. -/
def OrderedChain.Least {Node : Type} (o : OrderedChain Node) (x : Node) : Prop :=
  o.chain.members x ∧ ∀ y, o.chain.members y → y = x ∨ o.before x y

/-- Alignment only on selected endpoints; neither primitive is identified
with order by definition. Full and partial incoming edges are both covered. -/
def Aligned {Node : Type} (o : OrderedChain Node) : Prop :=
  ∀ y x, o.chain.members y → o.chain.members x →
    (o.before y x ↔ (o.chain.cause y x ∨ o.chain.partialCause y x))

theorem aligned_noFirst_iff {Node : Type} (o : OrderedChain Node)
    (align : Aligned o) : OrderedNoFirst o ↔ CausalNoFirst o.chain := by
  constructor
  · intro h; constructor
    rintro ⟨x, mx, source⟩
    exact h.noMinimum ⟨x, mx, fun y my edge => source y my ((align y x my mx).mp edge)⟩
  · intro h; constructor
    rintro ⟨x, mx, minimum⟩
    exact h.noMinimum ⟨x, mx, fun y my edge => minimum y my ((align y x my mx).mpr edge)⟩

theorem causal_noFirst_excludes_head {Node : Type} (c : Chain Node)
    (h : CausalNoFirst c) : ∀ x, ¬ c.Head x := by
  intro x head
  exact h.noMinimum ⟨x, head.1, head.2.2⟩

/-- Ordered minimality supports the existing externality step only with the
incoming-cause-to-order guard, productivity, and both-relation closure. -/
theorem ordered_minimum_uncaused {Node : Type} (o : OrderedChain Node) (x : Node)
    (closed : o.chain.Ungrounded) (mx : o.chain.members x)
    (productive : ∃ z, o.chain.members z ∧
      (o.chain.cause x z ∨ o.chain.partialCause x z))
    (minimum : ∀ y, o.chain.members y → ¬ o.before y x)
    (incoming : ∀ y, o.chain.members y →
      (o.chain.cause y x ∨ o.chain.partialCause y x) → o.before y x) :
    ∀ y, ¬ (o.chain.cause y x ∨ o.chain.partialCause y x) := by
  apply head_uncaused o.chain x closed
  exact ⟨mx, productive, fun y my edge => minimum y my (incoming y my edge)⟩


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

/-- A finite self-loop has no causal incoming minimum; cardinal infinity and
strict-order compatibility do not follow. -/
def loop : Chain Unit where
  members := fun _ => True
  cause := fun _ _ => True
  partialCause := fun _ _ => False

theorem finite_loop_noFirst : CausalNoFirst loop := by
  constructor
  rintro ⟨x, _, source⟩
  exact source x True.intro (Or.inl True.intro)

/-- An empty strict order can coexist with self-causation if alignment is omitted. -/
def unalignedLoop : OrderedChain Unit where
  chain := loop
  before := fun _ _ => False
  strictOrder := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }

theorem alignment_omission :
    CausalNoFirst unalignedLoop.chain ∧ ¬ OrderedNoFirst unalignedLoop := by
  refine ⟨finite_loop_noFirst, ?_⟩
  intro h
  exact h.noMinimum ⟨(), True.intro, fun _ _ h => h⟩

/-- Two incomparable isolated members: every member is minimal, none least.
Thus 'no least' is too weak to express the selected no-minimum reading. -/
def incomparable : OrderedChain Bool where
  chain := ⟨fun _ => True, fun _ _ => False, fun _ _ => False⟩
  before := fun _ _ => False
  strictOrder := { irrefl := fun _ h => h, trans := fun _ _ _ h _ => h }

theorem no_least_with_minima :
    (∀ x, ¬ incomparable.Least x) ∧ ¬ OrderedNoFirst incomparable := by
  constructor
  · intro x h
    cases x with
    | false => rcases h.2 true True.intro with bad | bad <;> cases bad
    | true => rcases h.2 false True.intro with bad | bad <;> cases bad
  · intro h
    exact h.noMinimum ⟨true, True.intro, fun _ _ h => h⟩


/-- A finite two-cycle also has no causal incoming minimum without self-loops. -/
def cycle : Chain Bool where
  members := fun _ => True
  cause := fun y x => y = !x
  partialCause := fun _ _ => False

theorem cycle_noFirst : CausalNoFirst cycle := by
  constructor
  rintro ⟨x, _, source⟩
  exact source (!x) True.intro (Or.inl rfl)

theorem infinite_history_noFirst : CausalNoFirst endless := by
  constructor
  rintro ⟨x, _, source⟩
  exact source (x + 1) True.intro (Or.inl rfl)

/-- Counting partial causes changes the answer even if there are no full causes. -/
def partialLoop : Chain Unit where
  members := fun _ => True
  cause := fun _ _ => False
  partialCause := fun _ _ => True

theorem partial_scope_matters :
    CausalNoFirst partialLoop ∧
    (∃ x, partialLoop.members x ∧ ∀ y, ¬ partialLoop.cause y x) := by
  refine ⟨?_, ⟨(), True.intro, fun _ h => h⟩⟩
  constructor
  rintro ⟨x, _, source⟩
  exact source x True.intro (Or.inr True.intro)

/-- Positive nonvacuity of the ordered reading: the integers under their usual
strict order have no minimal member. Int is only a control carrier; the
production primitives are empty here, so this witnesses OrderedNoFirst alone,
not alignment or any causal no-first claim. -/
def intOrder : OrderedChain Int where
  chain := ⟨fun _ => True, fun _ _ => False, fun _ _ => False⟩
  before := (· < ·)
  strictOrder := inferInstance

theorem int_ordered_noFirst : OrderedNoFirst intOrder := by
  constructor
  rintro ⟨x, _, minimum⟩
  exact minimum (x - 1) True.intro (by show x - 1 < x; omega)

end Controls
end TruthCore.Causality.EntireChainHead
