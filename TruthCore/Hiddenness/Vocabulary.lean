import TruthCore.Metaethics.AnswerMap

/-!
The independent hiddenness question set (#252). These are interpretation
parameters, not axioms or a new account of the first mover. Existing motion,
goodness and historical vocabularies do not represent time-indexed personal
access; no identification with them is silently imposed. A proposed identification
with the root's God requires a separate bridge, not the spelling of `God`.
-/
namespace TruthCore.Hiddenness

/-- Worlds index interpretations of the alleged necessary premises. `actual`
is where the empirical existential is asserted. No modal accessibility axioms
or inference to metaphysical possibility from a finite model are supplied. -/
structure Sig where
  World : Type
  Person : Type
  Time : Type
  actual : World
  God : World → Prop
  PerfectLove : World → Prop
  Capable : World → Person → Time → Prop
  /-- Resistance causally responsible for the absence of belief, rather than
  unrelated faults, lack of diligence, or a refusal already presupposing belief. -/
  Resists : World → Person → Time → Prop
  Believes : World → Person → Time → Prop
  HasConcept : World → Person → Time → Prop
  ReflectiveDoubt : World → Person → Time → Prop
  /-- Can enter a reciprocal conscious relationship just by trying now. -/
  Available : World → Person → Time → Prop
  /-- Freely accepts the relationship; distinct from believing God exists. -/
  Accepts : World → Person → Time → Prop
  /-- Positive sufficient reason for delaying explicit access, not merely an
  undetected reason. Whether such a reason exists is an open premise. -/
  GoodReason : World → Person → Time → Prop

/-- Schellenberg, Précis (2025), p. 2 premise 1 and p. 4: God-to-love,
quantified over the supplied worlds to represent his necessity claim. -/
def GodLoves (s : Sig) : Prop := ∀ w, s.God w → s.PerfectLove w

/-- Schellenberg, Précis (2025), p. 2 premise 2, p. 4 and p. 10 note 5.
Unqualified temporal openness: at every time of capacity, absent causal
resistance, love provides immediate conscious access. -/
def AlwaysOpen (s : Sig) : Prop :=
  ∀ w, s.PerfectLove w → ∀ p t, s.Capable w p t →
    ¬ s.Resists w p t → s.Available w p t

/-- Schellenberg, Précis (2025), p. 2 premise 3 and p. 4.
The negative source direction is retained. Conscious reciprocal access requires belief; this does not identify
belief with acceptance, knowledge, certainty, or constant felt presence. -/
def AccessNeedsBelief (s : Sig) : Prop :=
  ∀ w p t, ¬ s.Believes w p t → ¬ s.Available w p t

/-- Schellenberg, Précis (2025), p. 3 premise 5, p. 7 examples, p. 10.
The empirical premise, asserted at the actual world only. Neither sincere
seeking nor reasonable evidence alone is definitionally nonresistance. -/
def NonresistantNonbelief (s : Sig) : Prop :=
  ∃ p t, s.Capable s.actual p t ∧ ¬ s.Resists s.actual p t ∧
    ¬ s.Believes s.actual p t

/-- Positive rival account: lacking the concept blocks belief. Acquiring the
concept does not conversely guarantee belief or religious acceptance. -/
def ConceptNeeded (s : Sig) : Prop :=
  ∀ w p t, ¬ s.HasConcept w p t → ¬ s.Believes w p t

/-- Proposed developmental explanation of actual nonbelief: lack of access
to the concept or reflective doubt. Universal coverage is an explicit open
comparison premise, stronger than the source's examples and unattributed. -/
def DevelopmentalAccount (s : Sig) : Prop :=
  ∀ p t, ¬ s.Believes s.actual p t →
    ¬ s.HasConcept s.actual p t ∨ s.ReflectiveDoubt s.actual p t

def NoGod (s : Sig) : Prop := ¬ s.God s.actual

def GodExists (s : Sig) : Prop := s.God s.actual

/-- A reply's proposed constraint: each actual access failure for a capable
nonresister has a sufficient love-compatible reason. Explicitly open. -/
def ReasonForEachGap (s : Sig) : Prop :=
  ∀ w, s.God w → ∀ p t, s.Capable w p t → ¬ s.Resists w p t →
    ¬ s.Available w p t → s.GoodReason w p t

/-- A weaker access norm defended by the reply: without a sufficient reason
for delay, perfect love makes conscious access available. -/
def QualifiedOpen (s : Sig) : Prop :=
  ∀ w, s.PerfectLove w → ∀ p t, s.Capable w p t →
    ¬ s.Resists w p t → ¬ s.GoodReason w p t → s.Available w p t

/-- Belief can coexist with refusal: a counterexample to the claim that
revealing existence necessarily secures acceptance. -/
def BeliefWithoutAcceptancePossible : Prop :=
  ∃ s : Sig, ∃ p t, s.Believes s.actual p t ∧ ¬ s.Accepts s.actual p t

/-- A counterexample to deriving immediate access merely from perfect love
and a qualified norm. It makes no assertion about any actual divine reason. -/
def QualifiedDoesNotForceAlways : Prop :=
  ∃ s : Sig, GodLoves s ∧ QualifiedOpen s ∧ AccessNeedsBelief s ∧
    ReasonForEachGap s ∧ GodExists s ∧ NonresistantNonbelief s ∧ ¬ AlwaysOpen s

/-- None of the four advertised hiddenness premises can simply be deleted
while retaining the conclusion as a consequence of the other three. -/
def PremisesIndependent : Prop :=
  (∃ s : Sig, AlwaysOpen s ∧ AccessNeedsBelief s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s : Sig, GodLoves s ∧ AccessNeedsBelief s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s : Sig, GodLoves s ∧ AlwaysOpen s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s : Sig, GodLoves s ∧ AlwaysOpen s ∧ AccessNeedsBelief s ∧ GodExists s)

/-- Actual nonbelief with an exhibited sufficient-reason obligation. -/
def GapHasReason (s : Sig) : Prop :=
  ∃ p t, s.Capable s.actual p t ∧ ¬ s.Resists s.actual p t ∧
    ¬ s.Believes s.actual p t ∧ s.GoodReason s.actual p t

/-- Actual nonbelief with the developmental account's proposed mechanism. -/
def GapHasDevelopmentalAccount (s : Sig) : Prop :=
  ∃ p t, s.Capable s.actual p t ∧ ¬ s.Resists s.actual p t ∧
    ¬ s.Believes s.actual p t ∧
    (¬ s.HasConcept s.actual p t ∨ s.ReflectiveDoubt s.actual p t)

end TruthCore.Hiddenness
