import TruthCore.Greek.Plato.Forms

/-!
Issue #260: modern, deliberately limited tests of the participant-selection
objection. The shared Forms predicates retain their existing meanings. Nothing
here attributes a modern grounding calculus to Plato or Aristotle.

Research: Phaedo 100c–e leaves the manner open; Parmenides 131e and 132d–133a
challenge spatial/resemblance accounts, not every possible participation relation;
Metaphysics I.9 991a8–b9 separates being, knowledge and productive change.
-/
namespace TruthCore.Greek.Plato.ParticipationGrounding
open TruthCore.Greek.Plato.Forms

private instance : NeZero 4 where
  out h := Nat.noConfusion h

universe u v w
variable {Entity : Type u} {Quality : Type v} {Feature : Type w}

/-- Facts have distinct tags. In particular participation is not its own ground,
and a base fact is not defined as an already classified F fact. -/
inductive Fact (Entity : Type u) (Quality : Type v) (Feature : Type w) where
  | base : Entity → Feature → Fact Entity Quality Feature
  | participation : Entity → Entity → Fact Entity Quality Feature
  | exemplification : Entity → Quality → Fact Entity Quality Feature
  deriving DecidableEq

/-- A separately supplied explanatory interpretation. `Grounds a b` is directed
metaphysical dependence (ground to grounded fact), not material implication.
`Produces` concerns formative change; `Identifies` an agent's identification.
No bridges or success conditions for any of these relations are implicit. -/
structure Explanation (Entity : Type u) (Quality : Type v) (Feature : Type w) where
  Base : Entity → Feature → Prop
  Grounds : Fact Entity Quality Feature → Fact Entity Quality Feature → Prop
  Produces : Entity → Entity → Quality → Prop
  Identifies : Entity → Entity → Quality → Prop

/-- Optional classificatory coextension, restricted to particulars and Forms of
admitted qualities. It does not assert a grounding or causal relation. -/
def Coextension (s : Vocabulary Entity Quality) : Prop :=
  ∀ q f x, s.Admitted q → s.FormOf f q → s.Particular x →
    (s.Exemplifies x q ↔ s.Participates x f)

/-- A limited generic synthesis, not every commitment of every realist.
Even its putative `Explains` relation need not identify a participant-selector. -/
def Generic (s : Vocabulary Entity Quality) : Prop :=
  PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
  ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
  ExplanatoryParticipation s ∧ ExemplarParticipation s ∧ IntelligibleForms s ∧
  EssentialCharacterization s ∧ Coextension s

/-- Same stipulated nonassignment vocabulary. Actual exemplification,
participation and putative explanation of being F are intentionally excluded. -/
def SameBackground (s t : Vocabulary Entity Quality) : Prop :=
  s.Particular = t.Particular ∧ s.Admitted = t.Admitted ∧ s.FormOf = t.FormOf ∧
  s.Independent = t.Independent ∧ s.Intelligible = t.Intelligible ∧
  s.Unchanging = t.Unchanging ∧ s.ModelFor = t.ModelFor ∧
  s.Imitates = t.Imitates ∧ s.Like = t.Like ∧ s.Essentially = t.Essentially

/-- Additional, UNATTRIBUTED selection law. A feature is fixed independently
of the classificatory predicates; the law is not a consequence of naming it G. -/
def SelectionLaw (s : Vocabulary Entity Quality)
    (e : Explanation Entity Quality Feature) (feature : Feature) (form : Entity) : Prop :=
  ∀ x, s.Particular x → (s.Participates x form ↔ e.Base x feature)

/-- Separate additional UNATTRIBUTED explanatory commitment. A selector law
alone cannot establish this directed dependence. -/
def GroundedSelection (s : Vocabulary Entity Quality)
    (e : Explanation Entity Quality Feature) (feature : Feature) (form : Entity) : Prop :=
  ∀ x, s.Particular x → e.Base x feature →
    e.Grounds (.base x feature) (.participation x form)

/-- Optional explanatory norm, not a theorem about every sense of cause. -/
def AsymmetricGround (e : Explanation Entity Quality Feature) : Prop :=
  ∀ a b, e.Grounds a b → ¬ e.Grounds b a

/-- The two asserted explanatory directions, not the two directions of an iff.
Both edges concern the SAME bearer, Form and quality; they are explicit premises. -/
def CircularExplanation (e : Explanation Entity Quality Feature)
    (x f : Entity) (q : Quality) : Prop :=
  e.Grounds (.exemplification x q) (.participation x f) ∧
  e.Grounds (.participation x f) (.exemplification x q)

def NoCircularExplanation (e : Explanation Entity Quality Feature)
    (x f : Entity) (q : Quality) : Prop :=
  ¬ CircularExplanation e x f q

/-- Consequence tested below: selection laws with extensionally identical bases
and coextension force agreement in F-predication on common candidate bearers. -/
def ClassificationAgreement (s t : Vocabulary Entity Quality) : Prop :=
  ∀ q f x, s.Admitted q → t.Admitted q → s.FormOf f q → t.FormOf f q →
    s.Particular x → t.Particular x → (s.Exemplifies x q ↔ t.Exemplifies x q)

/-- Explicit premises of the selection test, not a purported Platonic axiom. -/
def SharedSelector (s t : Vocabulary Entity Quality)
    (e d : Explanation Entity Quality Feature) (feature : Feature) : Prop :=
  Coextension s ∧ Coextension t ∧
  (∀ x, e.Base x feature ↔ d.Base x feature) ∧
  (∀ q f, s.Admitted q → t.Admitted q → s.FormOf f q → t.FormOf f q →
    SelectionLaw s e feature f ∧ SelectionLaw t d feature f)

/-- Fixing the specified background and base does not fix the assignment. 0 is
one Form, 1 and 2 are candidate bearers (mnemonically Socrates/horse), 3 is an
additional bearer. These are formal labels, not rival biological facts. -/
def AssignmentUnderdetermined : Prop :=
  ∃ s t : Vocabulary (Fin 4) Unit,
  ∃ e : Explanation (Fin 4) Unit Unit,
    Generic s ∧ Generic t ∧ SameBackground s t ∧
    (∀ x, e.Base x () ↔ (x = 3 ∨ x = 1)) ∧
    s.Particular 1 ∧ t.Particular 1 ∧ s.FormOf 0 () ∧ t.FormOf 0 () ∧
    s.Participates 1 0 ∧ ¬ t.Participates 1 0 ∧
    s.Exemplifies 1 () ∧ ¬ t.Exemplifies 1 () ∧
    (∀ a b, ¬ e.Grounds a b)

/-- A noncircular selection model with immanent base, separate exemplar and
formative relation. It supplies consistency, NOT the truth or adequacy of those
additional mechanisms. Same F/participation facts also admit an empty account. -/
def GroundingIndependent : Prop :=
  ∃ s : Vocabulary (Fin 4) Unit,
  ∃ e d : Explanation (Fin 4) Unit Unit,
    Generic s ∧ e.Base = d.Base ∧
    SelectionLaw s e () 0 ∧ SelectionLaw s d () 0 ∧
    GroundedSelection s e () 0 ∧ AsymmetricGround e ∧
    e.Base 1 () ∧ ¬ e.Base 2 () ∧
    s.ModelFor 0 1 ∧ s.Essentially 0 () ∧
    e.Grounds (.base 1 ()) (.participation 1 0) ∧
    ¬ d.Grounds (.base 1 ()) (.participation 1 0) ∧
    e.Produces 0 1 () ∧ ¬ d.Produces 0 1 () ∧
    e.Identifies 2 1 () ∧ ¬ d.Identifies 2 1 ()

end TruthCore.Greek.Plato.ParticipationGrounding
