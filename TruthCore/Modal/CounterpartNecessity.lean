import TruthCore.German.Kant.CosmologicalInference

/-! Issue #470. Stipulative counterpart semantics, separate from canonical
rigid identity. No historical attribution or metaphysical possibility claim.
The four-place relation is deliberately issue-local: similarity is not equality. -/
namespace TruthCore.Modal.CounterpartNecessity
open TruthCore.German.Kant.CosmologicalInference
variable {W B : Type}
abbrev Relation (W B : Type) := W → B → W → B → Prop

/-- An existing bearer has an existing counterpart at every accessible world. -/
def CounterpartNecessaryAt (m : Ontic W B) (c : Relation W B) (w : W) (x : B) : Prop :=
  m.ExistsAt w x ∧ ∀ v, m.frame.access w v → ∃ y, m.ExistsAt v y ∧ c w x v y
/-- Totality on existing bearers, only along accessible edges. -/
def Total (m : Ontic W B) (c : Relation W B) : Prop :=
  ∀ w x, m.ExistsAt w x → ∀ v, m.frame.access w v → ∃ y, m.ExistsAt v y ∧ c w x v y
/-- Functional on the existing target domain. -/
def Unique (m : Ontic W B) (c : Relation W B) : Prop :=
  ∀ w x v y z, m.ExistsAt v y → m.ExistsAt v z → c w x v y → c w x v z → y = z
/-- Injective on existing source and target domains. -/
def Injective (m : Ontic W B) (c : Relation W B) : Prop :=
  ∀ w x z v y, m.ExistsAt w x → m.ExistsAt w z → m.ExistsAt v y →
    c w x v y → c w z v y → x = z
/-- Substantive numerical-identity bridge; bijection alone does not supply it. -/
def IdentityBridge (c : Relation W B) : Prop := ∀ w x v y, c w x v y → x = y

theorem identity_recovers_rigid (m : Ontic W B) (c : Relation W B) (w : W) (x : B)
    (h : CounterpartNecessaryAt m c w x) (hi : IdentityBridge c) : NecessaryAt m w x := by
  intro v hv
  obtain ⟨y, hy, hc⟩ := h.2 v hv
  rw [hi w x v y hc]
  exact hy

/-- Two universal-access worlds, each with its own distinct sole inhabitant. -/
def alternating : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => x = w
  Causes := fun _ _ _ => False
/-- The unique inhabitants correspond, including self correspondence. -/
def paired : Relation Bool Bool := fun w x v y => x = w ∧ y = v

theorem paired_total : Total alternating paired := by
  intro w x hx v _
  exact ⟨v, rfl, hx, rfl⟩
theorem paired_unique : Unique alternating paired := by
  intro w x v y z hy hz _ _
  exact hy.trans hz.symm
theorem paired_injective : Injective alternating paired := by
  intro w x z v y hx hz _ _ _
  exact hx.trans hz.symm
/-- Even total functional injective correspondence in both directions leaves
no rigid necessary bearer; the per-world maps are singleton bijections. -/
theorem separation : CounterpartNecessaryAt alternating paired false false ∧
    ¬ NecessaryBeing alternating false ∧ ¬ IdentityBridge paired := by
  refine ⟨⟨rfl, paired_total false false rfl⟩, ?_, ?_⟩
  · rintro ⟨x, hx, hn⟩
    have ht := hn true True.intro
    change x = false at hx
    change x = true at ht
    cases hx.symm.trans ht
  · intro h
    have bad := h false false true true ⟨rfl, rfl⟩
    cases bad

/-- Removing cross-world links preserves functionality and injectivity but
loses totality and counterpart necessity, despite a populated target world. -/
def missing : Relation Bool Bool := fun w x v y => w = v ∧ x = w ∧ y = v

theorem missing_discriminates : Unique alternating missing ∧ Injective alternating missing ∧
    ¬ CounterpartNecessaryAt alternating missing false false := by
  refine ⟨?_, ?_, ?_⟩
  · intro w x v y z hy hz _ _
    exact hy.trans hz.symm
  · intro w x z v y hx hz _ _ _
    exact hx.trans hz.symm
  · intro h
    obtain ⟨y, _, hc⟩ := h.2 true True.intro
    cases hc.1

/-- Both source inhabitants map to the sole target inhabitant. -/
def merging : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun w x => w = false ∨ x = false
  Causes := fun _ _ _ => False
def mergeLinks : Relation Bool Bool := fun _ _ _ y => y = false

theorem many_to_one_discriminates : Total merging mergeLinks ∧ Unique merging mergeLinks ∧
    CounterpartNecessaryAt merging mergeLinks false true ∧
    ¬ Injective merging mergeLinks ∧ ¬ NecessaryAt merging false true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w x _ v _
    exact ⟨false, Or.inr rfl, rfl⟩
  · intro w x v y z _ _ hy hz
    exact hy.trans hz.symm
  · exact ⟨Or.inl rfl, fun _ _ => ⟨false, Or.inr rfl, rfl⟩⟩
  · intro h
    have bad := h false false true true false (Or.inl rfl) (Or.inl rfl)
      (Or.inr rfl) rfl rfl
    cases bad
  · intro h
    rcases h true True.intro with bad | bad <;> cases bad
/-- Every target inhabitant has a source counterpart: the paired maps are
surjective as well as total, functional and injective. -/
theorem paired_surjective : ∀ w v y, alternating.ExistsAt v y →
    ∃ x, alternating.ExistsAt w x ∧ paired w x v y := by
  intro w v y hy
  exact ⟨w, rfl, rfl, hy⟩

/-- Cross-world links in both directions, but no reflexive links. -/
def crossOnly : Relation Bool Bool := fun w x v y => w ≠ v ∧ x = w ∧ y = v

theorem nontransitive_discriminates :
    crossOnly false false true true ∧ crossOnly true true false false ∧
    ¬ crossOnly false false false false ∧
    ¬ CounterpartNecessaryAt alternating crossOnly false false := by
  refine ⟨⟨by decide, rfl, rfl⟩, ⟨by decide, rfl, rfl⟩, ?_, ?_⟩
  · intro h
    exact h.1 rfl
  · intro h
    obtain ⟨y, _, hc⟩ := h.2 false True.intro
    exact hc.1 rfl

/-- Literal same-individual control: false exists at both worlds. -/
def rigid : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ x => x = false
  Causes := fun _ _ _ => False

theorem rigid_control : NecessaryBeing rigid false ∧
    CounterpartNecessaryAt rigid (fun _ x _ y => x = y) false false := by
  exact ⟨⟨false, rfl, fun _ _ => rfl⟩,
    ⟨rfl, fun _ _ => ⟨false, rfl, rfl⟩⟩⟩

/-- Closed conjunction of the separating model and omission controls. Rigid
recovery is separately conditional on IdentityBridge, not defended here. -/
def Controls : Prop :=
  (NecessaryBeing rigid false ∧
    CounterpartNecessaryAt rigid (fun _ x _ y => x = y) false false) ∧
  Total alternating paired ∧ Unique alternating paired ∧ Injective alternating paired ∧
  (∀ w v y, alternating.ExistsAt v y → ∃ x, alternating.ExistsAt w x ∧ paired w x v y) ∧
  (CounterpartNecessaryAt alternating paired false false ∧
    ¬ NecessaryBeing alternating false ∧ ¬ IdentityBridge paired) ∧
  (Unique alternating missing ∧ Injective alternating missing ∧
    ¬ CounterpartNecessaryAt alternating missing false false) ∧
  (Total merging mergeLinks ∧ Unique merging mergeLinks ∧
    CounterpartNecessaryAt merging mergeLinks false true ∧
    ¬ Injective merging mergeLinks ∧ ¬ NecessaryAt merging false true) ∧
  (crossOnly false false true true ∧ crossOnly true true false false ∧
    ¬ crossOnly false false false false ∧
    ¬ CounterpartNecessaryAt alternating crossOnly false false)

theorem controls : Controls :=
  ⟨rigid_control, paired_total, paired_unique, paired_injective, paired_surjective, separation,
    missing_discriminates, many_to_one_discriminates, nontransitive_discriminates⟩
end TruthCore.Modal.CounterpartNecessity
