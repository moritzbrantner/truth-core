/-!
A shared interface for the Forms readings of Phaedo 99d–102a, Parmenides
128e–130e, Republic V 475e–480a / X 596a–598c and Timaeus 27d–29b / 51b–52d.

This interface asserts no theory. Forms and particulars inhabit the SAME type:
nonidentity and self-predication are commitments, never consequences of typing.
`Admitted` restricts the range of Forms; it need not contain human, fire or dirt.
The predicates for explanation, independence and essential characterization are
uninterpreted philosophical vocabulary. Satisfying them in a finite model tests
formal compatibility only; it supplies no philosophical explanation.
-/
namespace TruthCore.Greek.Plato.Forms

universe u v

structure Vocabulary (Entity : Type u) (Quality : Type v) where
  Particular : Entity → Prop
  Admitted : Quality → Prop
  FormOf : Entity → Quality → Prop
  Exemplifies : Entity → Quality → Prop
  Participates : Entity → Entity → Prop
  Independent : Entity → Prop
  Intelligible : Entity → Prop
  Unchanging : Entity → Prop
  Explains : Entity → Entity → Quality → Prop
  ModelFor : Entity → Entity → Prop
  Imitates : Entity → Entity → Prop
  Like : Entity → Entity → Prop
  Essentially : Entity → Quality → Prop

variable {Entity : Type u} {Quality : Type v}

/-- Republic 476a / 479a: a bounded phenomenon, two distinct F particulars.
This does not identify the respect in which a thing is F with every respect. -/
def PropertyInstances (s : Vocabulary Entity Quality) : Prop :=
  ∃ x y q, x ≠ y ∧ s.Particular x ∧ s.Particular y ∧ s.Admitted q ∧
    s.Exemplifies x q ∧ s.Exemplifies y q

/-- Republic 596a–b, restricted to admitted qualities: one common Form for the
F particulars. Participation here is classificatory; no explanation follows. -/
def OneOverMany (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∃ f, s.FormOf f q ∧
    ∀ x, s.Particular x → s.Exemplifies x q → s.Participates x f

/-- Republic 596a–b: numerical uniqueness of the Form for an admitted quality. -/
def UniqueForms (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f g, s.FormOf f q → s.FormOf g q → f = g

/-- Phaedo 100c–e, thin reading: participating particulars are F.
The converse for F particulars is in OneOverMany, not in the vocabulary. -/
def ParticipationPredication (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f x, s.FormOf f q → s.Particular x →
    s.Participates x f → s.Exemplifies x q

/-- Republic 476c–d / Parmenides 130b, numerical separation reading only. -/
def Nonidentity (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f x, s.FormOf f q → s.Particular x →
    s.Participates x f → f ≠ x

/-- Parmenides 130b, ontological reading of 'separately': an independent Form.
This is a separate open predicate, not a proved modal account of independence. -/
def OntologicalSeparation (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f, s.FormOf f q → s.Independent f

/-- Phaedo 100c–e, explanatory reading: an F particular is F through a Form.
No presence, sharing, spatial part, temporal event or efficient cause is specified. -/
def ExplanatoryParticipation (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ x, s.Particular x → s.Exemplifies x q →
    ∃ f, s.FormOf f q ∧ s.Participates x f ∧ s.Explains f x q

/-- Republic 596b, schematic artisan exemplar reading, restricted to the
admitted artifact qualities and corresponding particulars in that reading. -/
def ExemplarParticipation (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ x, s.Particular x → s.Exemplifies x q →
    ∃ f, s.FormOf f q ∧ s.ModelFor f x ∧ s.Imitates x f

/-- Timaeus 51d–52a: Forms admitted in this reading are intelligible and stable.
This is a projection, not an encoding of all three kinds including the receptacle. -/
def IntelligibleForms (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f, s.FormOf f q → s.Intelligible f ∧ s.Unchanging f

/-- Optional UNATTRIBUTED generalization: the Form F itself exemplifies F
in the same predicative sense as a particular. No dialogue-wide axiom is asserted. -/
def UniformSelfPredication (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f, s.FormOf f q → s.Exemplifies f q

/-- Optional UNATTRIBUTED essential-characterization alternative. There is no
bridge from this predicate to ordinary exemplification. -/
def EssentialCharacterization (s : Vocabulary Entity Quality) : Prop :=
  ∀ q, s.Admitted q → ∀ f, s.FormOf f q → s.Essentially f q

/-- Phaedo 100b–c: literal self-predicative reading of 'beautiful itself',
for the designated beauty quality alone, not every Form. -/
def BeautySelfPredication (s : Vocabulary Entity Quality) (beauty : Quality) : Prop :=
  ∃ f, s.FormOf f beauty ∧ s.Exemplifies f beauty

/-- Sibling reading of the same expression: essential characterization alone. -/
def BeautyEssentialCharacterization
    (s : Vocabulary Entity Quality) (beauty : Quality) : Prop :=
  ∃ f, s.FormOf f beauty ∧ s.Essentially f beauty

/-- Timaeus 29a–b: the cosmos is an image of a stable intelligible model.
The model is not silently identified with the generated cosmos's maker/cause. -/
def CosmosExemplar (s : Vocabulary Entity Quality) (cosmos : Entity) : Prop :=
  ∃ f, s.Intelligible f ∧ s.Unchanging f ∧ s.ModelFor f cosmos ∧ s.Imitates cosmos f

/-- Parmenides 130c: whether a human Form is admitted remains undecided here.
This explicit candidate commitment is NOT attributed to the young Socrates. -/
def HumanFormAdmitted (s : Vocabulary Entity Quality) (human : Quality) : Prop :=
  s.Admitted human

end TruthCore.Greek.Plato.Forms
