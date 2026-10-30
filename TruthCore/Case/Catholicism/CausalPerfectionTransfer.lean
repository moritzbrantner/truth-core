import TruthCore.Case.Catholicism.StageOneQuartaVia
import TruthCore.Logic.StrengthComparison
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2

/-! A scope comparison, not a new source attribution. See the semantic dossier
in docs/notes/causal-perfection-transfer.md. `CausesIn` retains effective causal
responsibility, including mediated primary causation if independently justified;
it is not defined as mere enabling or counterfactual dependence. -/
namespace TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.StrengthComparison

/-- Open transfer principle restricted to sources of every other actual being.
The scope condition is the existing `CausesAllInGenus` at esse, independently of
God, maximality, or causation of other perfections. Self-effects are excluded.
The additional esse antecedent keeps this a literal restriction of the legacy
principle without assuming actuality-to-being. Neither universality alone nor
q.44 a.1 proves this principle. -/
def UniversalCauseTransfersPerfections {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ c, CausesAllInGenus InAct CausesIn esse c →
    ∀ x r, x ≠ c → CausesIn c x esse → InAct x r → CausesIn c x r

/-- Exactly the omitted causal cases: nonuniversal sources, and self-effects.
This is a residual scope obligation, not a defense of those cases. -/
def ResidualPerfectionTransfer {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  (∀ c, ¬ CausesAllInGenus InAct CausesIn esse c →
    ∀ x r, CausesIn c x esse → InAct x r → CausesIn c x r) ∧
  (∀ c r, CausesIn c c esse → InAct c r → CausesIn c c r)

/-- Scope comparison under explicit decisions of identity and of the universal
causal condition. These decisions are comparison parameters, not new assumptions
of the naming or goodness applications. -/
def perfectionTransferSpec (Being Respect : Type) [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)] : ComparisonSpec where
  stronger := CauseOfBeingCausesEveryPerfection InAct CausesIn esse
  weaker := UniversalCauseTransfersPerfections InAct CausesIn esse
  delta := ResidualPerfectionTransfer InAct CausesIn esse

/-- Four role positions: 0 universal existential source, 1 particular existential supporter, 2 skilled
secondary producer, 3 recipient. All exist and have the tested perfection.
False = esse, true = skill. This records causal responsibility, not uniqueness
of sufficient determination. The role interpretation is schematic, not physics. -/
inductive TransferRole where
  | source | supporter | producer | recipient
  deriving DecidableEq

def transferAct (_ : TransferRole) (_ : Bool) : Prop := True

def transferCause (concurrent : Bool) (c x : TransferRole) (r : Bool) : Prop :=
  if r = false then (c = .source ∧ x ≠ .source) ∨ (c = .supporter ∧ x = .recipient)
  else if concurrent = true then (c = .source ∧ x ≠ .source) ∨ (c = .producer ∧ x = .recipient)
  else c = .producer ∧ x ≠ .producer

/-- Strict order of ranks for each respect; the rival puts the secondary producer
above the existential source in skill, while keeping source 0 first in esse. -/
def transferRank (concurrent : Bool) (r : Bool) (c : TransferRole) : Nat :=
  if r = false ∨ concurrent = true then (match c with
    | .source => 4 | .supporter => 3 | .producer => 2 | .recipient => 1)
  else if c = .producer then 5 else (match c with
    | .source => 4 | .supporter => 3 | .producer => 2 | .recipient => 1)

def transferMore (concurrent : Bool) (r : Bool) (c x : TransferRole) : Prop :=
  transferRank concurrent r c > transferRank concurrent r x

/-- Direct exhaustive decision on the four causal roles, without the axiom
used by the core Fin enumeration. This domain is an interpretation's cast of
roles, not a replacement for a mathematical finite-set notion. -/
@[instance_reducible] def transferFourForallDecidable
    (p : TransferRole → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .source ∧ p .supporter ∧ p .producer ∧ p .recipient)
    ⟨fun h x => match x with
      | .source => h.1 | .supporter => h.2.1
      | .producer => h.2.2.1 | .recipient => h.2.2.2,
      fun h => ⟨h .source, h .supporter, h .producer, h .recipient⟩⟩

attribute [local instance] transferFourForallDecidable

instance transferUniversalDecidable (b : Bool) :
    DecidablePred (CausesAllInGenus transferAct (transferCause b) false) :=
by
  intro c
  unfold CausesAllInGenus transferAct transferCause
  infer_instance

/-- Closed setting for the strict scope separator. -/
def concurrentTransferSetting : ComparisonSpec :=
  perfectionTransferSpec TransferRole Bool transferAct (transferCause true) false

/-- Exact decomposition of the unrestricted principle under the explicitly
supplied finite-style decisions; no philosophical necessity is asserted. -/
def PerfectionTransferExactDelta : Prop := ∀ (Being Respect : Type) [DecidableEq Being]
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    [DecidablePred (CausesAllInGenus InAct CausesIn esse)],
    CauseOfBeingCausesEveryPerfection InAct CausesIn esse ↔
      UniversalCauseTransfersPerfections InAct CausesIn esse ∧
      ResidualPerfectionTransfer InAct CausesIn esse

/-- The specified populated setting separates universal from unrestricted scope. -/
def ScopeTransferSeparates : Prop := Separation concurrentTransferSetting

/-- Both readings satisfy the shared genus, strict ascent, actuality-to-being,
and formal/eminent preexistence background. Each has a supplied maximum 0 and
universal esse source 0 with no distinct incoming esse cause. All four beings
have both actualities. No assumption about God is used. -/
def TransferModelBackground (b : Bool) : Prop :=
  MaximumInGenusCausesAllInGenusReading transferAct (transferMore b) (transferCause b) ∧
  TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
    (transferCause b) (transferMore b) ∧
  (∀ x r, transferAct x r → transferAct x false) ∧
  PerfectionsOfEffectPreexistInCauseReading transferAct (transferCause b) false ∧
  IsMaximumIn transferAct (transferMore b) false .source ∧
  CausesAllInGenus transferAct (transferCause b) false .source ∧
  (∀ c, c ≠ .source → ¬ transferCause b c .source false) ∧
  transferCause b .supporter .recipient false ∧ transferCause b .producer .recipient true

/-- A model witnesses a narrower bridge with a genuine excluded particular-source case. -/
def ConcurrentTransferSeparates : Prop :=
  TransferModelBackground true ∧ Separation concurrentTransferSetting

/-- Existential dependence and all the shared background survive when the
secondary producer alone causes skill, including skill in source 0. No temporal
or modal law, no God predicate, and no application of the naming premise is
asserted by this rival witness. -/
def SecondaryOnlyTransferSurvives : Prop :=
  TransferModelBackground false ∧
  ¬ UniversalCauseTransfersPerfections transferAct (transferCause false) false
end TruthCore.Case.Catholicism
