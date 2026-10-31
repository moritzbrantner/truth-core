import TruthCore.Explanation.CondensationSufficiency
import TruthCore.Explanation.JointCooperation

/-! Analyst vocabulary for #741 over the #733 `Exercise` and the #734 `Supply`.
A power profile `cap s e` says that the bearer of event `e` has the power for
that exercise at scenario `s`. Having the power and exercising it are separate:
`occurs` is the exercise. `Borrowed` asks whether the power is present only under
a lender; it mentions no source, no termination and no well-foundedness, so a
regress of borrowed events is expressible and is witnessed below. `cap` is a
supplied parameter, for one selected respect; nothing here decides which profile
is the real one, and `Supply` stays a proposed standard, not a defended account of
production. See docs/notes/borrowed-exercise-741.md. -/
namespace TruthCore.Explanation.BorrowedExercise
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.JointCooperation (NecessaryIn)

variable {B E G S : Type}

/-- A record that lends at scenario `s`: admitted, with at least one contributor,
all contributors occurring at `s`, and at the actual scenario also exercised.
`Exercise` has exercise data for the actual scenario only. -/
def Lender (m : Exercise B E G S) (s : S) (g : G) : Prop :=
  m.groups.admitted g ∧ (s = m.actual → m.exercised g) ∧
    (m.groups.contributors g).Nonempty ∧ ∀ c ∈ m.groups.contributors g, m.occurs s c

/-- Some lending record at `s` has `e` as its effect. -/
def Lent (m : Exercise B E G S) (s : S) (e : E) : Prop :=
  ∃ g, Lender m s g ∧ m.groups.effect g = e

/-- At every allowed scenario where the power is present, a lender is present.
This holds vacuously of an event whose power is absent at every allowed scenario. -/
def Borrowed (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  ∀ s, m.allowed s → cap s e → Lent m s e

/-- The power is present at some allowed scenario with no lender present. -/
def Retained (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  ∃ s, m.allowed s ∧ cap s e ∧ ¬ Lent m s e

/-- Actual exercise under an actual lender, of a power present only under a lender. -/
def Instrument (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  Borrowed m cap e ∧ m.occurs m.actual e ∧ Lent m m.actual e

/-- Actual exercise under an actual lender, of a power retained without one. -/
def Secondary (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  Retained m cap e ∧ m.occurs m.actual e ∧ Lent m m.actual e

/-- Actual exercise with no actual lender. It does not say the exercise is uncaused
or explained: only that no record in this `Exercise` lends to it. -/
def SelfExercising (m : Exercise B E G S) (e : E) : Prop :=
  m.occurs m.actual e ∧ ¬ Lent m m.actual e

/-- Actual exercise of a retained power. -/
def OwnActive (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  m.occurs m.actual e ∧ Retained m cap e

/-- The power is present at every allowed scenario. -/
def Essential (m : Exercise B E G S) (cap : S → E → Prop) (e : E) : Prop :=
  ∀ s, m.allowed s → cap s e

/-- Records lending at the actual scenario. -/
def lentGroups (m : Exercise B E G S) : Groups E G :=
  { m.groups with admitted := Lender m m.actual }

/-- No actual exercise without the power for it. -/
def PowerRequired (m : Exercise B E G S) (cap : S → E → Prop) : Prop :=
  ∀ e, m.occurs m.actual e → cap m.actual e

/-- Analyst reading under test: every exercise under an actual lender is of a
borrowed power. It is compared with, and not identified with, the attributed
statement STMT-WHATEVER-MOVES-AND-IS-MOVED-MOVES-AS-INSTRUMENT. -/
def MovedMoversInstruments (m : Exercise B E G S) (cap : S → E → Prop) : Prop :=
  ∀ e, m.occurs m.actual e → Lent m m.actual e → Borrowed m cap e

/-- A nonempty self-contained set of actually lent exercises: none meets `I`, and
each lending record for a member keeps a contributor among the members. -/
def Descent (m : Exercise B E G S) (I : E → Prop) (e : E) (D : Set E) : Prop :=
  e ∈ D ∧ (∀ x ∈ D, m.occurs m.actual x ∧ Lent m m.actual x) ∧ Trap (lentGroups m) I D

/-- An actual lending chain from `e` through events satisfying `P`. -/
def Chain (m : Exercise B E G S) (P : E → Prop) (e : E) (f : Nat → E) : Prop :=
  f 0 = e ∧ ∀ n, P (f n) ∧ ∃ g, Lender m m.actual g ∧ m.groups.effect g = f n ∧
    f (n + 1) ∈ m.groups.contributors g

/-- The chain has no repeated event. -/
def Regress (m : Exercise B E G S) (P : E → Prop) (e : E) : Prop :=
  ∃ f, Chain m P e f ∧ Function.Injective f

/-- The chain revisits an event. -/
def Circle (m : Exercise B E G S) (P : E → Prop) (e : E) : Prop :=
  ∃ f, Chain m P e f ∧ ∃ i j, i < j ∧ f i = f j

/-- Each clause for every `Exercise` and profile, under its own hypotheses. -/
def Forks : Prop :=
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    Retained m cap e ↔ ¬ Borrowed m cap e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    m.allowed m.actual → PowerRequired m cap → m.occurs m.actual e →
      (Instrument m cap e ∨ Secondary m cap e ∨ SelfExercising m e) ∧
      ¬ (Instrument m cap e ∧ Secondary m cap e) ∧
      ¬ (Instrument m cap e ∧ SelfExercising m e) ∧
      ¬ (Secondary m cap e ∧ SelfExercising m e)) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (e : E), m.occurs m.actual e →
    Supply (lentGroups m) (SelfExercising m) e ∨
      ∃ D, Descent m (SelfExercising m) e D) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    m.allowed m.actual → PowerRequired m cap → m.occurs m.actual e →
    Supply (lentGroups m) (OwnActive m cap) e ∨
      ∃ D, Descent m (OwnActive m cap) e D ∧ ∀ x ∈ D, Instrument m cap x) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (I : E → Prop) (e : E) (D : Set E),
    Descent m I e D → ¬ Supply (lentGroups m) I e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (I P : E → Prop) (e : E) (D : Set E),
    Descent m I e D → (∀ x ∈ D, P x) → Regress m P e ∨ Circle m P e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (I : E → Prop) (e : E),
    Supply (lentGroups m) I e → Supply m.exercisedGroups I e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (I : E → Prop) (e : E),
    m.coherent → (∀ x, I x → m.occurs m.actual x) → Supply (lentGroups m) I e →
      m.occurs m.actual e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (e : E),
    WellFounded (lentGroups m).graph.edge → m.occurs m.actual e →
      Supply (lentGroups m) (SelfExercising m) e)

/-- Supply on the self-exercise standard gives Supply on the own-power standard.
The reading under test gives the converse; `SecondaryRegress` refutes the converse
without it. -/
def Collapse : Prop :=
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    m.allowed m.actual → PowerRequired m cap →
      Supply (lentGroups m) (SelfExercising m) e → Supply (lentGroups m) (OwnActive m cap) e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    m.allowed m.actual → PowerRequired m cap → MovedMoversInstruments m cap →
      (OwnActive m cap e ↔ SelfExercising m e) ∧
      (Supply (lentGroups m) (OwnActive m cap) e ↔ Supply (lentGroups m) (SelfExercising m) e)) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (cap : S → E → Prop) (e : E),
    m.allowed m.actual → PowerRequired m cap → MovedMoversInstruments m cap →
    m.occurs m.actual e → Supply (lentGroups m) (SelfExercising m) e ∨
      ∃ D, Descent m (SelfExercising m) e D ∧ ∀ x ∈ D, Instrument m cap x)

/-! ## One source-free exercise, two power profiles -/

/-- #734 `unrooted`, unchanged, is the exercise in both regress witnesses. -/
abbrev chain := unrooted

/-- Power present only when exercised. -/
def capOccurs (m : Exercise B E G S) : S → E → Prop := m.occurs

/-- Power present at every scenario. -/
def capAll : S → E → Prop := fun _ _ => True

/-- `chain` with `capOccurs`: every event is an instrument, on an injective lending
chain, with no Supply on either standard. The exercise is coherent and sufficient. -/
def InstrumentRegress : Prop :=
  chain.coherent ∧ (∀ g, chain.jointlySufficient g) ∧
  (∀ s, LocalPower unrootedGroups (fun _ => False) (chain.occurs s)) ∧
  PowerRequired chain (capOccurs chain) ∧
  MovedMoversInstruments chain (capOccurs chain) ∧
  (∀ n, Instrument chain (capOccurs chain) n) ∧
  (∀ n, Regress chain (Instrument chain (capOccurs chain)) n) ∧
  (∀ n, ¬ Supply (lentGroups chain) (OwnActive chain (capOccurs chain)) n) ∧
  (∀ n, ¬ Supply (lentGroups chain) (SelfExercising chain) n)

/-- `chain` with `capAll`: every event is a secondary cause on the same graph with
the same occurrence. Supply holds on the own-power standard and fails on the
self-exercise standard, and the reading under test fails. -/
def SecondaryRegress : Prop :=
  PowerRequired chain capAll ∧
  ¬ MovedMoversInstruments chain capAll ∧
  (∀ n, Secondary chain capAll n) ∧
  (∀ n, Supply (lentGroups chain) (OwnActive chain capAll) n) ∧
  (∀ n, ¬ Supply (lentGroups chain) (SelfExercising chain) n) ∧
  (∀ n, Regress chain (Secondary chain capAll) n)

/-- `chain` restricted to the on scenario. The profile `capAll` retained nothing at
this smaller scenario space: every event is an instrument. -/
def selectedChain : Exercise Nat Nat Nat Bool :=
  { chain with allowed := fun s => s = true }

def SelectedCollapse : Prop :=
  selectedChain.coherent ∧
  (∀ n, Instrument selectedChain capAll n) ∧
  (∀ n, ¬ Supply (lentGroups selectedChain) (OwnActive selectedChain capAll) n)

/-! ## Instruments with a source, and a circle -/

/-- #634 through #734 `rooted`, unchanged: a self-exercising source occurring at
every allowed scenario, with every branch event an instrument without Supply. -/
def RootedBranch : Prop :=
  PowerRequired rooted (capOccurs rooted) ∧
  SelfExercising rooted (node none) ∧ NecessaryIn rooted (node none) ∧
  Supply (lentGroups rooted) (OwnActive rooted (capOccurs rooted)) (node none) ∧
  (∀ n, Instrument rooted (capOccurs rooted) (node (some n))) ∧
  (∀ n, ¬ Supply (lentGroups rooted) (OwnActive rooted (capOccurs rooted)) (node (some n)))

/-- #734 `circle`: the two events lend to each other at the on scenario. -/
def circleExercise : Exercise Bool Bool Bool Bool where
  groups := circle
  bearer := id
  occurs := fun s _ => s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

def InstrumentCircle : Prop :=
  circleExercise.coherent ∧ (∀ g, circleExercise.jointlySufficient g) ∧
  (∀ e, Instrument circleExercise (capOccurs circleExercise) e) ∧
  (∀ e, Circle circleExercise (Instrument circleExercise (capOccurs circleExercise)) e) ∧
  (∀ e, ¬ Supply (lentGroups circleExercise)
    (OwnActive circleExercise (capOccurs circleExercise)) e)

open TruthCore.Explanation.CondensationSufficiency in
/-- #752's two record structures on one membership graph, under the same scenario
data and the same profile: t is an instrument in both, with Supply in one only. -/
def RecordControl : Prop :=
  conj.graph = disj.graph ∧
  (onOff conj everyScenario).coherent ∧ (onOff disj everyScenario).coherent ∧
  Instrument (onOff conj everyScenario) (capOccurs (onOff conj everyScenario)) .t ∧
  Instrument (onOff disj everyScenario) (capOccurs (onOff disj everyScenario)) .t ∧
  ¬ Supply (lentGroups (onOff conj everyScenario))
    (OwnActive (onOff conj everyScenario) (capOccurs (onOff conj everyScenario))) .t ∧
  Supply (lentGroups (onOff disj everyScenario))
    (OwnActive (onOff disj everyScenario) (capOccurs (onOff disj everyScenario))) .t

/-! ## Finite founded exercises -/

/-- #734 `finite` as an exercise: `false` contributes to `true`, at the on scenario. -/
def finiteExercise : Exercise Bool Bool Unit Bool where
  groups := finite
  bearer := id
  occurs := fun s _ => s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

/-- Power of `false` at every scenario, power of `true` only when exercised. -/
def capSource (s : Bool) (e : Bool) : Prop := e = false ∨ s = true

/-- `false` self-exercises under profiles where its power is and is not essential;
`true` is an instrument with own-power Supply under both, so that Supply does not
separate the two. The exercise of `false` does not occur at every allowed scenario,
whereas the source in `RootedBranch` does. With `capAll`, `true` is a secondary
cause and has Supply on both standards. -/
def FoundedControls : Prop :=
  finiteExercise.coherent ∧
  Instrument finiteExercise capSource true ∧
  SelfExercising finiteExercise false ∧
  Essential finiteExercise capSource false ∧
  Supply (lentGroups finiteExercise) (OwnActive finiteExercise capSource) true ∧
  Instrument finiteExercise (capOccurs finiteExercise) true ∧
  ¬ Essential finiteExercise (capOccurs finiteExercise) false ∧
  OwnActive finiteExercise (capOccurs finiteExercise) false ∧
  Supply (lentGroups finiteExercise) (OwnActive finiteExercise (capOccurs finiteExercise)) true ∧
  ¬ NecessaryIn finiteExercise false ∧
  Secondary finiteExercise capAll true ∧
  Supply (lentGroups finiteExercise) (OwnActive finiteExercise capAll) true ∧
  Supply (lentGroups finiteExercise) (SelfExercising finiteExercise) true

/-- `false` occurs under a profile with no power at all: borrowed only vacuously,
with no own-power Supply and no descent. So the conclusion of the power fork fails
at this event when `PowerRequired` is dropped. -/
def PowerOmission : Prop :=
  ¬ PowerRequired finiteExercise (fun _ _ => False) ∧
  Borrowed finiteExercise (fun _ _ => False) false ∧
  ¬ Supply (lentGroups finiteExercise) (OwnActive finiteExercise fun _ _ => False) false ∧
  ¬ ∃ D, Descent finiteExercise (OwnActive finiteExercise fun _ _ => False) false D

/-- An empty record seeds Supply in the #734 sense without an intrinsic event but
does not lend here. An unexercised record with occurring contributors does not lend
either, so `SelfExercising` is relative to the exercise data. -/
def LenderOmissions : Prop :=
  Supply emptyRecord (fun _ => False) () ∧
  (∀ m : Exercise Unit Unit Unit Unit, m.groups = emptyRecord → ¬ Lent m m.actual ()) ∧
  finiteExercise.jointlySufficient () ∧
  SelfExercising { finiteExercise with exercised := fun _ => False } true

def Certificate : Prop :=
  Forks ∧ Collapse ∧ InstrumentRegress ∧ SecondaryRegress ∧ SelectedCollapse ∧
  RootedBranch ∧ InstrumentCircle ∧ RecordControl ∧ FoundedControls ∧
  PowerOmission ∧ LenderOmissions

end TruthCore.Explanation.BorrowedExercise
