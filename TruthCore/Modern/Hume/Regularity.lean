import TruthCore.Metaethics.AnswerMap

/-! #270. Analytical causal tests, not a reconstruction of all Humean metaphysics.
The source readings are separately recorded against materialized Enquiry VII,
Lewis 1994 §§3–4, Woodward §§4.3/4.6, and Hartle–Hawking pp.2960–2961.
Experiments describe complete deterministic binary response tables. They assume
ideal surgical settings; observed correlations do not establish those settings.
No modal/induction vocabulary is duplicated from the adjacent investigations. -/
namespace TruthCore.Modern.Hume.Regularity

/-- Enquiry VII.29's first definition, on stipulated similarity/succession
relations. No intervention or psychological clause is silently added. -/
def RegularCause {E : Type} (similar follows : E → E → Prop) (a b : E) : Prop :=
  follows a b ∧ ∀ a', similar a a' → ∃ b', similar b b' ∧ follows a' b'

/-- VII.29's second definition; a mental transition is distinct from succession. -/
def MentalCause {E : Type} (follows transition : E → E → Prop) (a b : E) : Prop :=
  follows a b ∧ transition a b

structure Experiment where
  /-- U indexes two background contexts, not two possible worlds. -/
  x : Bool → Bool
  y : Bool → Bool
  /-- Y under setting X, with U fixed; the intervention overrides X's equation. -/
  setX : Bool → Bool → Bool
  /-- X under setting Y, with U fixed. -/
  setY : Bool → Bool → Bool

def Conjunction (m : Experiment) : Prop := ∀ u, m.x u = m.y u

def Nontrivial (m : Experiment) : Prop := m.x false ≠ m.x true

def Changes (response : Bool → Bool → Bool) : Prop :=
  ∃ u, response u false ≠ response u true

def SameObservations (m n : Experiment) : Prop :=
  (∀ u, m.x u = n.x u) ∧ (∀ u, m.y u = n.y u)

/-- U→X→Y; setting Y leaves X alone. -/
def chain : Experiment := ⟨id, id, fun _ x => x, fun u _ => u⟩
/-- U→Y→X; observationally identical to chain. -/
def reverseChain : Experiment := ⟨id, id, fun u _ => u, fun _ y => y⟩
/-- U→X and U→Y. Setting X does not change Y. -/
def fork : Experiment := ⟨id, id, fun u _ => u, fun u _ => u⟩

/-- A non-vacuous fork refutes the observational-conjunction→efficacy rule,
conditional on intervention response being the intended sense of efficacy. -/
def ConfoundingTest : Prop :=
  Conjunction fork ∧ Nontrivial fork ∧ ¬ Changes fork.setX ∧
    ¬ (∀ m : Experiment, Conjunction m → Changes m.setX)

/-- Undirected observations do not choose causal direction. -/
def DirectionTest : Prop :=
  SameObservations chain reverseChain ∧ Changes chain.setX ∧ ¬ Changes chain.setY ∧
    ¬ Changes reverseChain.setX ∧ Changes reverseChain.setY

/-- Hume's 'followed by' is extra structure. Time order breaks the reversal
symmetry but a lagged common-cause observation still need not be effective.
The chosen times 1 and 2 are model stipulations, not empirical findings. -/
def TemporalTest : Prop :=
  (1 < 2) ∧ ¬ (2 < 1) ∧ Conjunction fork ∧ ¬ Changes fork.setX

/-- Two independent variables, sampled only on the diagonal. Off-sample
observations break the apparent law: this is selection/coincidence, not a
common-cause model. No frequency or chance claim is encoded. -/
def sample (u : Bool × Bool) : Prop := u.1 = u.2

def CoincidenceTest : Prop :=
  (∀ u : Bool × Bool, sample u → u.1 = u.2) ∧
    (∃ u : Bool × Bool, ¬ sample u ∧ u.1 ≠ u.2)

/-- A surgical contrast distinguishes a chain from its observationally identical
fork. Once the full response table is supplied, efficacy is determined. This
is the strongest immediate reply to an attack on the entire mosaic: the
counterexample used only a small observational projection, not all facts. -/
def InterventionTest : Prop :=
  SameObservations chain fork ∧ Changes chain.setX ∧ ¬ Changes fork.setX ∧
    (∀ m n : Experiment, (∀ u x, m.setX u x = n.setX u x) →
      (Changes m.setX ↔ Changes n.setX))

/-- Finite evidence alone leaves the next value open; a specified globally
valid law does entail its prediction. The second clause is elementary
instantiation, explicitly a conditional, not a solution to induction. -/
def PredictionTest : Prop :=
  (∀ cutoff : Nat, ∃ f g : Nat → Bool,
    (∀ n, n < cutoff → f n = g n) ∧ f cutoff ≠ g cutoff) ∧
  (∀ (f : Nat → Bool) (b : Bool), (∀ n, f n = b) → ∀ n, f n = b)

/-- Lewis 1994 §3 schematic identification of laws with theorems of the best
true system. Selection of that system, natural predicates, strength and
simplicity are substantive additional inputs, not supplied by this interface. -/
def BestSystemReading {R : Type} (law theoremOfSelected : R → Prop) : Prop :=
  ∀ r, law r ↔ theoremOfSelected r

/-- A deliberately finite candidate-language demonstration: actual validity
of a regularity is insufficient for lawhood when only selected theorems count.
This is not an algorithm that computes Lewis's actual best system. -/
inductive Regularity where
  | pattern | incidental
  deriving DecidableEq

def trueRegularity (_ : Regularity) : Prop := True

def selectedTheorem (r : Regularity) : Prop := r = .pattern

def BestSystemTest : Prop :=
  BestSystemReading selectedTheorem selectedTheorem ∧
    trueRegularity .pattern ∧ trueRegularity .incidental ∧
    selectedTheorem .pattern ∧ ¬ selectedTheorem .incidental

/-- A process within spacetime and spacetime considered as a whole are
comparison targets, not two events or two substances in an established ontology. -/
inductive Target where
  | process | spacetime
  deriving DecidableEq

structure Scope where
  temporalCause : Target → Target → Prop
  /-- Explanatory grounding; not identified with earlier temporal production. -/
  ground : Target → Target → Prop

def Within (t : Target) : Prop := t = .process

def LocalCausality (s : Scope) : Prop :=
  ∀ t, Within t → ∃ c, s.temporalCause c t

def GroundedTotality (s : Scope) : Prop := ∃ g, s.ground g .spacetime

def UniversalGrounding (s : Scope) : Prop := ∀ t, ∃ g, s.ground g t

/-- A hypothetical interlocutor, NOT Hume or Hartle–Hawking: ordinary
processes have temporal causes; the totality has no explanatory ground. -/
def brute : Scope := ⟨fun _ t => t = .process, fun _ t => t = .process⟩
/-- Same local causal facts and no earlier cause of totality, yet a ground. -/
def grounded : Scope := ⟨fun _ t => t = .process, fun _ _ => True⟩

def BoundaryTest : Prop :=
  (LocalCausality brute ∧ ¬ GroundedTotality brute) ∧
  (LocalCausality grounded ∧ GroundedTotality grounded ∧
    ¬ (∃ c, grounded.temporalCause c .spacetime)) ∧
  (∀ s, UniversalGrounding s → GroundedTotality s) ∧
  ¬ (∀ s, LocalCausality s → GroundedTotality s) ∧
  ¬ (∀ s, LocalCausality s → ¬ GroundedTotality s)

/-- Shared questions are identical for each selected account; U is genuinely
unexplained. Source answers are recorded in docs/hume-regularity.md; this map
records the formal answers, whose availability is narrower. -/
inductive Question where
  | confounding | direction | coincidence | intervention | prediction | grounding
  deriving DecidableEq

inductive Account where
  | bare | enriched | scopedBrute
  deriving DecidableEq

def testAnswer : Question → Prop
  | .confounding => ConfoundingTest
  | .direction => DirectionTest
  | .coincidence => CoincidenceTest
  | .intervention => InterventionTest
  | .prediction => PredictionTest
  | .grounding => BoundaryTest

/-- Naive extrapolation claims tested against the enriched account. These
are stipulated analytical theses, not historical attributions. -/
def bareAnswer : Question → Prop
  | .confounding | .intervention =>
      ∀ m : Experiment, Conjunction m → Changes m.setX
  | .direction => ∀ m n : Experiment, SameObservations m n →
      (Changes m.setX ↔ Changes n.setX)
  | .coincidence => ∀ u : Bool × Bool, u.1 = u.2
  | .prediction => ∀ (cutoff : Nat) (f g : Nat → Bool),
      (∀ n, n < cutoff → f n = g n) → f cutoff = g cutoff
  | .grounding => False

/-- The selected complete answers over this six-question signature. Enriched
answers the five ordinary diagnostics through response tables, sample limits
and the need for a granted law. ScopedBrute adds a hypothetical brute totality;
its existential consistency is verified, not its truth of the actual cosmos.
Bare offers five sufficiency claims, each defeated by the tests. The unfilled
cosmic slots are unexplained, not negative existential answers. -/
def ordinaryAvailability : Question → Prop
  | .confounding => True
  | .direction => True
  | .coincidence => True
  | .intervention => True
  | .prediction => True
  | .grounding => False

def bruteAnswer : Question → Prop
  | .confounding => ConfoundingTest
  | .direction => DirectionTest
  | .coincidence => CoincidenceTest
  | .intervention => InterventionTest
  | .prediction => PredictionTest
  | .grounding => LocalCausality brute ∧ ¬ GroundedTotality brute

def formalAnswers : Account → TruthCore.Metaethics.AnswerMap Question
  | .bare => ⟨ordinaryAvailability, bareAnswer⟩
  | .enriched => ⟨ordinaryAvailability, testAnswer⟩
  | .scopedBrute => ⟨fun _ => True, bruteAnswer⟩

def AnswerMapTest : Prop :=
  (∀ q, q ≠ Question.grounding →
    ¬ TruthCore.Metaethics.CommittedAt (formalAnswers .bare) q) ∧
  (∀ q, q ≠ Question.grounding →
    TruthCore.Metaethics.CommittedAt (formalAnswers .enriched) q) ∧
  ¬ (formalAnswers .enriched).answers .grounding ∧
  TruthCore.Metaethics.CommittedAt (formalAnswers .scopedBrute) .grounding

/-- All formal stress tests. Their conjunction certifies models/conditional
laws, not an actual metaphysics, law-selection standard or cosmogenesis. -/
def Checks : Prop :=
  ConfoundingTest ∧ DirectionTest ∧ TemporalTest ∧ CoincidenceTest ∧
  InterventionTest ∧ PredictionTest ∧ BestSystemTest ∧ BoundaryTest ∧ AnswerMapTest

end TruthCore.Modern.Hume.Regularity
