module

public import TruthCore.Logic.JustificationIntrospection

/-!
Analyst formulations for #1053, attribution deferred. K is a world-indexed
knowledge operator and R concerns possible circumstances of knowing the SAME
content. Neither world indices nor K silently quantify over agents or times.
The relational specialization uses the existing fixed-agent epistemic box.
-/

@[expose] public section

namespace TruthCore.Logic.FitchKnowability
open TruthCore.Modal

/-- The actual world, modal alternatives and an epistemic operator are separate.
No relation between modal and epistemic alternatives is built in. -/
structure Context (W : Type) where
  modal : Frame W
  actual : W
  knows : (W → Prop) → W → Prop

/-- A truth at a world that is not known at THAT world. -/
def Moore {W : Type} (c : Context W) (p : W → Prop) (w : W) : Prop :=
  p w ∧ ¬ c.knows p w

/-- The same predicate is known at some modally accessible world. -/
def PossibleKnown {W : Type} (c : Context W) (p : W → Prop) (w : W) : Prop :=
  ∃ v, c.modal.access w v ∧ c.knows p v

/-- Only two laws, for this Moore content at relevant witness worlds: factivity
and left-conjunct extraction. Laws merely at the actual world do not suffice. -/
def RelevantLaws {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  ∀ v, c.modal.access c.actual v →
    (c.knows (Moore c p) v → Moore c p v) ∧
    (c.knows (Moore c p) v → c.knows p v)

/-- A sufficient stronger background, at every world and for all contents. -/
def GlobalLaws {W : Type} (c : Context W) : Prop :=
  (∀ q w, c.knows q w → q w) ∧
  (∀ p q w, c.knows (fun v => p v ∧ q v) w → c.knows p w ∧ c.knows q w)

/-- The Moore content cannot be known in any modal alternative to actuality. -/
def MooreUnknowable {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  ¬ PossibleKnown c (Moore c p) c.actual

/-- The single knowability instance needed by this argument. -/
def MooreInstance {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  Moore c p c.actual → PossibleKnown c (Moore c p) c.actual

/-- Constructive consequence: truth excludes negated knowledge, but supplies
no proof of knowledge without a further stability principle. -/
def DoubleNegatedKnowledge {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  p c.actual → ¬¬ c.knows p c.actual

/-- Explicit stability of this one actual knowledge proposition; weaker than
unrestricted classical double-negation elimination. -/
def KnowledgeStable {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  (¬¬ c.knows p c.actual) → c.knows p c.actual

/-- A conditional for one content and one actual world, not an agent-existence
or common-knower conclusion. -/
def TruthKnown {W : Type} (c : Context W) (p : W → Prop) : Prop :=
  p c.actual → c.knows p c.actual

/-- Restricted forward knowability at actuality. -/
def RestrictedKnowability {W : Type} (c : Context W) (C : (W → Prop) → Prop) : Prop :=
  ∀ q, C q → q c.actual → PossibleKnown c q c.actual

/-- Whether the problematic content is in the domain is an explicit bridge. -/
def MooreAdmissible {W : Type} (c : Context W) (C : (W → Prop) → Prop)
    (p : W → Prop) : Prop := C (Moore c p)

/-- Every admissible content satisfies the biconditional at EVERY world.
The reverse direction is additional to ordinary forward knowability. -/
def GlobalRestrictedEquivalence {W : Type} (c : Context W)
    (C : (W → Prop) → Prop) : Prop :=
  ∀ q, C q → ∀ w, q w ↔ PossibleKnown c q w

/-- A semantic surrogate for epistemic-free Boolean contents over a single
nonconstant atom: contents agree whenever the atom's truth values agree. -/
def AtomInvariant {W : Type} (atom q : W → Prop) : Prop :=
  ∀ u v, (atom u ↔ atom v) → (q u ↔ q v)

/-- The admissible family includes the atom and constants and is closed under
ordinary conjunction, disjunction and negation. Moore closure is separate. -/
def BooleanClosed {W : Type} (C : (W → Prop) → Prop) : Prop :=
  C (fun _ => True) ∧ C (fun _ => False) ∧
  (∀ p q, C p → C q → C (fun w => p w ∧ q w)) ∧
  (∀ p q, C p → C q → C (fun w => p w ∨ q w)) ∧
  (∀ p, C p → C (fun w => ¬ p w))

-- Avoid the default computed NeZero proof in finite numeral elaboration.
local instance : NeZero 4 := ⟨Nat.noConfusion⟩

/-- The nonconstant basic atom is true at worlds zero and two. -/
def survivorAtom (w : Fin 4) : Prop := w = 0 ∨ w = 2

/-- Epistemic S5 blocks {0,1}, {2}, {3}: uncertainty at the first pair. -/
def survivorEpistemic : Frame (Fin 4) where
  access u v := (u.val < 2 ∧ v.val < 2) ∨ u = v

/-- Modal S5 blocks {0,2}, {1,3}: possible learning preserves the atom. -/
def survivorModal : Frame (Fin 4) where
  access u v := survivorAtom u ↔ survivorAtom v

/-- World zero is actual, with the already defined relational knowledge. -/
def survivorContext : Context (Fin 4) where
  modal := survivorModal
  actual := 0
  knows := JustificationIntrospection.Knows survivorEpistemic

/-- Concrete four-world rival, both frames S5. The epistemic frame E is NOT a
subrelation of modal R; no compatibility premise may be inferred from this
witness. This witnesses a stipulated formal interpretation, not actual human
knowledge, an intuitionistic countermodel, or the truth of antirealism. -/
def RestrictedSurvivor : Prop :=
  let E := survivorEpistemic
  let c := survivorContext
  let p := survivorAtom
  c.knows = JustificationIntrospection.Knows E ∧
    Reflexive E ∧ Symmetric E ∧ Transitive E ∧
    Reflexive c.modal ∧ Symmetric c.modal ∧ Transitive c.modal ∧
    GlobalLaws c ∧ BooleanClosed (AtomInvariant p) ∧ AtomInvariant p p ∧
    GlobalRestrictedEquivalence c (AtomInvariant p) ∧
    Moore c p c.actual ∧ ¬ MooreAdmissible c (AtomInvariant p) p ∧
    ¬ (∀ u v, E.access u v → c.modal.access u v)

end TruthCore.Logic.FitchKnowability
