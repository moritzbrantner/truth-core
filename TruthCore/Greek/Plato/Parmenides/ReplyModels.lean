import TruthCore.Greek.Plato.Parmenides.ParticipationChallenges

namespace TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
open TruthCore.Greek.Plato.Forms

/-- A witness reuses the previously checked separated-causal synthesis, with two
particulars and one Form, while refusing all spatial whole/part allocations. -/
def NonspatialPossible : Prop :=
  ∃ (s : Vocabulary (Fin 3) Unit) (m : Mereology (Fin 3)),
    PropertyInstances s ∧ OneOverMany s ∧ UniqueForms s ∧
    ParticipationPredication s ∧ Nonidentity s ∧ OntologicalSeparation s ∧
    ExplanatoryParticipation s ∧ IndivisibleForms s m ∧ WholeExclusive m ∧
    NoSpatialDilemma s m

/-- Non-inherent, independent Forms can be interpreted as asymmetric grounds
without interpreting them as change-producers. Compatibility is not adequacy.
The witness includes a non-vacuous explanatory pair. -/
def GroundReplyPossible : Prop :=
  ∃ (s : Vocabulary Bool Unit) (g : Explanation Bool) (rank : Bool → Nat),
    OntologicalSeparation s ∧ Nonidentity s ∧ ExplanatoryParticipation s ∧
    ExplanationGrounds s g ∧ NoninherentForms s g ∧ RankedGround g rank ∧
    AsymmetricGround g ∧ NoImmanenceRequirement g ∧
    (∃ f x q, s.FormOf f q ∧ s.Particular x ∧ s.Explains f x q) ∧
    (∀ f x, ¬g.ProducesChange f x)

/-- Two directions of mediated cognition can cross the encoded realm boundary:
no object is identified with its presentation. Entity and agent argument roles
both use Bool here; no claim about their philosophical identity is made.
A divine mode is merely an interpreted label, not a proof of a god's existence. -/
def MediationPossible : Prop :=
  ∃ (s : Vocabulary Bool Unit) (k : Cognition Bool Bool),
    HumanOutside k ∧ DivineInside k ∧ MediatedTransfer k ∧ HumanRoute s k ∧
    NoKnowledgeRealmClosure s k ∧
    (∃ a x, k.Divine a ∧ ¬s.Intelligible x ∧ k.Knows a x)

/-- Concrete test interpretation: true is a Form, false a particular. This has
one particular; the separate nonspatial witness supplies the two-particular test.
Grounding and cognition below use these same entity extensions. -/
def replyForms : Vocabulary Bool Unit where
  Particular x := x = false
  Admitted _ := True
  FormOf f _ := f = true
  Exemplifies _ _ := True
  Participates x f := x = false ∧ f = true
  Independent f := f = true
  Intelligible f := f = true
  Unchanging f := f = true
  Explains f x _ := f = true ∧ x = false
  ModelFor f x := f = true ∧ x = false
  Imitates x f := x = false ∧ f = true
  Like _ _ := False
  Essentially _ _ := False

def replyGround : Explanation Bool where
  Inheres _ _ := False
  Ground f x := f = true ∧ x = false
  ProducesChange _ _ := False

def replyRank (x : Bool) : Nat := if x then 0 else 1

/-- false is the human mode; true the divine/intelligible mode. Each directly
cognizes a presentation on its own side, then knows an object on the other.
Presents is intentionally not symmetric likeness, identity or efficient cause.
This is a test of a transfer premise, not a theory of how truth is recognized. -/
def replyCognition : Cognition Bool Bool where
  Human a := a = false
  Divine a := a = true
  IntelligibleAgent a := a = true
  Knows a f := a ≠ f
  Direct a r := a = r
  Presents r f := r ≠ f

end TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
