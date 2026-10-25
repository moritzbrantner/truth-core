import TruthCore.Greek.Plato.Forms

/-! Bounded readings of Parmenides 130e–131e and 133b–134e.
This extension reuses Forms entities and participation. Its additional relations
are independent: identity, spatial presence, proper part, inherence, explanatory
grounding, change production and cognition are never identified by typing.
The modern conditions below are explicit open premises, not historical axioms. -/
namespace TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
open TruthCore.Greek.Plato.Forms
universe u v w

structure Mereology (E : Type u) where
  ProperPart : E → E → Prop
  WholeAt : E → E → Prop
  Allocated : E → E → Prop

/-- 130e–131a, dilemma on the distributive spatial reading only. -/
def SpatialDilemma {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (m : Mereology E) : Prop :=
  ∀ x f, s.Participates x f →
    m.WholeAt f x ∨ ∃ p, m.ProperPart p f ∧ m.Allocated p x

/-- Unattributed spatial exclusion premise needed by the whole horn.
Numerical nonidentity alone does not entail it. -/
def WholeExclusive {E : Type u} (m : Mereology E) : Prop :=
  ∀ f x y, m.WholeAt f x → m.WholeAt f y → x = y

/-- The no-division commitment of 131b, deliberately explicit. -/
def IndivisibleForms {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (m : Mereology E) : Prop :=
  ∀ q, s.Admitted q → ∀ f, s.FormOf f q → ∀ p, ¬m.ProperPart p f

def NoSpatialDilemma {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (m : Mereology E) : Prop := ¬SpatialDilemma s m

structure Explanation (E : Type u) where
  Inheres : E → E → Prop
  Ground : E → E → Prop
  ProducesChange : E → E → Prop

/-- Aristotle 991a8–19 motivates the challenge. This schematic non-inherence
reading is distinct from mere numerical difference and ontological independence. -/
def NoninherentForms {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (g : Explanation E) : Prop :=
  ∀ q, s.Admitted q → ∀ f x, s.FormOf f q → s.Particular x → ¬g.Inheres f x

/-- OPEN modern reconstruction of the demand that being-F explanation is ground. -/
def ExplanationGrounds {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (g : Explanation E) : Prop :=
  ∀ f x q, s.Explains f x q → g.Ground f x

/-- OPEN immanence requirement, not a theorem about all forms of causation. -/
def GroundRequiresInherence {E : Type u} (g : Explanation E) : Prop :=
  ∀ f x, g.Ground f x → g.Inheres f x

def NoImmanenceRequirement {E : Type u} (g : Explanation E) : Prop :=
  ¬GroundRequiresInherence g

/-- A rank is a mathematical witness for strict asymmetric dependence, not time.
This condition does not produce changes or prove an explanation adequate. -/
def RankedGround {E : Type u} (g : Explanation E) (rank : E → Nat) : Prop :=
  ∀ f x, g.Ground f x → rank f < rank x

def AsymmetricGround {E : Type u} (g : Explanation E) : Prop :=
  ∀ f x, g.Ground f x → ¬g.Ground x f

structure Cognition (E : Type u) (A : Type w) where
  Human : A → Prop
  Divine : A → Prop
  IntelligibleAgent : A → Prop
  Knows : A → E → Prop
  Direct : A → E → Prop
  Presents : E → E → Prop

/-- 134a–e, the disputed closure principle projected onto knowledge.
For human agents it requires non-intelligible objects; for intelligible agents
intelligible objects. It is stronger than numerical or ontological separation. -/
def KnowledgeRealmClosure {E : Type u} {Q : Type v} {A : Type w}
    (s : Vocabulary E Q) (k : Cognition E A) : Prop :=
  ∀ a x, k.Knows a x → (k.IntelligibleAgent a ↔ s.Intelligible x)

def HumanOutside {E : Type u} {A : Type w} (k : Cognition E A) : Prop :=
  ∀ a, k.Human a → ¬k.IntelligibleAgent a

/-- Only the conditional divine horn: divine agents taking this mode are on the
intelligible side. Neither a god's existence nor omniscience is assumed. -/
def DivineInside {E : Type u} {A : Type w} (k : Cognition E A) : Prop :=
  ∀ a, k.Divine a → k.IntelligibleAgent a

/-- Both directions of the greatest difficulty, restricted to the encoded modes. -/
def CrossRealmIgnorance {E : Type u} {Q : Type v} {A : Type w}
    (s : Vocabulary E Q) (k : Cognition E A) : Prop :=
  (∀ a, k.Human a → ∀ f, s.Intelligible f → ¬k.Knows a f) ∧
  (∀ a, k.Divine a → ∀ x, ¬s.Intelligible x → ¬k.Knows a x)

/-- Phaedo 74b–d motivates cognition through another object. This modern
universal transfer rule is OPEN: mere likeness or perception does not imply it.
Direct tracks successful cognition of a presentation, not bare sensation. -/
def MediatedTransfer {E : Type u} {A : Type w} (k : Cognition E A) : Prop :=
  ∀ a r f, k.Direct a r → k.Presents r f → k.Knows a f

/-- A successful mediation route, whose soundness still needs justification. -/
def HumanRoute {E : Type u} {Q : Type v} {A : Type w}
    (s : Vocabulary E Q) (k : Cognition E A) : Prop :=
  ∃ a r f, k.Human a ∧ s.Intelligible f ∧ k.Direct a r ∧ k.Presents r f

def NoKnowledgeRealmClosure {E : Type u} {Q : Type v} {A : Type w}
    (s : Vocabulary E Q) (k : Cognition E A) : Prop := ¬KnowledgeRealmClosure s k

/-- OPEN cross-dialogue causal reply: a stable exemplar can guide a distinct
producer. Timaeus 28a–b motivates the division of roles, not this universal
sufficiency condition or the maker’s numerical distinctness from every model. -/
def ModelMakerBridge {E : Type u} {Q : Type v}
    (s : Vocabulary E Q) (g : Explanation E) : Prop :=
  ∀ f x, s.ModelFor f x → ∃ maker, maker ≠ f ∧ g.ProducesChange maker x

end TruthCore.Greek.Plato.Parmenides.ParticipationChallenges
