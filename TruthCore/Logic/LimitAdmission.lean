module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover
public import TruthCore.Causality.Supertasks

/-! # Limit admission (#486)
Analyst formulations, attribution deferred. Ambient convergence and closedness
are Mathlib topology. Modal profiles compare worlds; they are not successive
physical operations. Event occupancy and endpoint state are independent data.
No physical realizability or necessary being follows from these definitions. -/

@[expose] public section
namespace TruthCore.Logic.LimitAdmission
open Filter Topology
open TruthCore.Causality
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

/-- Closed admission is an additional policy on a subset of an ambient space.
Its applicability to worlds, events, or physical states remains OPEN. -/
def ClosedAdmission {X : Type} [TopologicalSpace X] (A : Set X) : Prop := IsClosed A

/-- Two universal conditional laws: ambient closure membership, and admission
under separately supplied closedness plus membership of every stage. -/
def ClosureLaws : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (f : ℕ → X) (x : X),
    Tendsto f atTop (𝓝 x) →
    x ∈ closure (Set.range f) ∧
    ∀ A : Set X, ClosedAdmission A → Set.range f ⊆ A → x ∈ A

/-- Boolean encoding of the EXISTING Nat-tail presence predicate. Rigid
candidate identity and the actualist extension agree exactly with #533. -/
def tailProfile (n : ℕ) : ℕ → Bool := fun b => if n ≤ b then true else false
def falseProfile : ℕ → Bool := fun _ => false
def tailWorlds : Set (ℕ → Bool) := Set.range tailProfile

/-- Conditional application of the common schema in the modal product space.
This does not assert that the admitted world set actually is closed. -/
def ModalTransfer : Prop :=
  ∀ W : Set (ℕ → Bool), ClosedAdmission W → tailWorlds ⊆ W → falseProfile ∈ W

/-- Tail worlds omit every finite list jointly and converge to the empty
profile, but never admit it. Closedness is exactly the omitted bridge here. -/
def ModalBoundary : Prop :=
  FiniteCoverControls ∧
  (∀ n b, tailProfile n b = true ↔ finiteCoverTailPresent b n) ∧
  (∀ xs : List ℕ, ∃ n, ∀ b ∈ xs, tailProfile n b = false) ∧
  Tendsto tailProfile atTop (𝓝 falseProfile) ∧
  falseProfile ∈ closure tailWorlds ∧ falseProfile ∉ tailWorlds ∧
  ¬ ClosedAdmission tailWorlds ∧
  (ClosedAdmission (closure tailWorlds) ∧ falseProfile ∈ closure tailWorlds)

/-- Event times approaching the first time point from above. The ambient time
interval includes zero; it does not thereby contain an event at zero. -/
noncomputable def eventTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def eventTimes : Set ℝ := Set.range eventTime

/-- Closure of event occupancy is a distinct temporal policy. -/
def TemporalTransfer : Prop :=
  ∀ E : Set ℝ, ClosedAdmission E → eventTimes ⊆ E → (0 : ℝ) ∈ E

/-- A bounded-duration event history without a first event, despite a first
time point. Taking its closure gives a mathematical positive admission model,
not evidence that nature supplies that closure policy. -/
def TemporalBoundary : Prop :=
  Tendsto eventTime atTop (𝓝 0) ∧
  (∀ n, 0 < eventTime n ∧ eventTime n ≤ 1) ∧
  IsLeast (Set.Icc (0 : ℝ) 1) 0 ∧
  (0 : ℝ) ∈ closure eventTimes ∧ (0 : ℝ) ∉ eventTimes ∧
  (∀ t ∈ eventTimes, ∃ u ∈ eventTimes, u < t) ∧
  ¬ ClosedAdmission eventTimes ∧
  (ClosedAdmission (closure eventTimes) ∧ (0 : ℝ) ∈ closure eventTimes)

/-- Reciprocal schedule on the EXISTING supertask moments. Its choice differs
from the geometric schedule only to test the exact reciprocal example #486. -/
noncomputable def stageTime (n : ℕ) : ℝ := 1 - eventTime n
def stageEvents : Set ℝ := Set.range stageTime
noncomputable def momentTime : SupertaskMoment → ℝ
  | .stage n => stageTime n
  | .limit => 1

/-- Endpoint outcomes are assignments separate from finite-stage outputs.
The coherence policy requires actual convergence TO the assigned endpoint;
it does not follow from merely assigning a clock time to that endpoint. -/
def TerminalOutcome (state : SupertaskMoment → Bool) : Prop :=
  Tendsto (fun n => state (.stage n)) atTop (𝓝 (state .limit))

/-- Every finite-stage output is true while the endpoint is assigned false.
This is an abstract assignment, not a continuous or physically admissible law. -/
def mismatchedState : SupertaskMoment → Bool
  | .stage _ => true
  | .limit => false

/-- Closed event occupancy supplies an endpoint event. Separately, convergence
of state to b AND endpoint coherence supply that endpoint's state b. -/
def SupertaskTransfer : Prop :=
  (∀ E : Set ℝ, ClosedAdmission E → stageEvents ⊆ E → (1 : ℝ) ∈ E) ∧
  (∀ (state : SupertaskMoment → Bool) (b : Bool),
    Tendsto (fun n => state (.stage n)) atTop (𝓝 b) →
    TerminalOutcome state → state .limit = b)

/-- Timing, event occurrence, state convergence, and endpoint assignment are
separate. The same convergent timing supports both a stable and an oscillating
stage sequence; even stable stages do not fix an arbitrary endpoint assignment.
The abstract existing endpoint theorem is retained without physical upgrade. -/
def SupertaskBoundary : Prop :=
  EndlessStagesWithStableEndpoint ∧
  Tendsto stageTime atTop (𝓝 (1 : ℝ)) ∧ StrictMono stageTime ∧
  (¬ ∃ n, SupertaskMoment.stage n = .limit) ∧
  (∀ n, 0 ≤ stageTime n ∧ stageTime n < 1) ∧
  (∀ n, momentTime (.stage n) < momentTime .limit) ∧
  (1 : ℝ) ∈ closure stageEvents ∧ (1 : ℝ) ∉ stageEvents ∧
  ¬ ClosedAdmission stageEvents ∧
  (ClosedAdmission (closure stageEvents) ∧ (1 : ℝ) ∈ closure stageEvents) ∧
  (∀ b : Bool, ¬ Tendsto AlternatingStageOutput atTop (𝓝 b)) ∧
  Tendsto (fun n => mismatchedState (.stage n)) atTop (𝓝 true) ∧
  ¬ TerminalOutcome mismatchedState ∧
  TerminalOutcome (fun _ => true)

/-- All three typed omission controls and the shared conditional transfers.
These are mathematical consequences, not actual-domain admission assertions. -/
def Package : Prop :=
  ClosureLaws ∧ ModalTransfer ∧ TemporalTransfer ∧ SupertaskTransfer ∧
  ModalBoundary ∧ TemporalBoundary ∧ SupertaskBoundary

/-- Independent inputs of the closed-admission rule, kept as named statement
heads so binding exposes convergence, closedness, and containment separately. -/
def Converges {X : Type} [TopologicalSpace X] (f : ℕ → X) (x : X) : Prop :=
  Tendsto f atTop (𝓝 x)
def StagesAdmitted {X : Type} (f : ℕ → X) (A : Set X) : Prop := Set.range f ⊆ A
def LimitAdmitted {X : Type} (x : X) (A : Set X) : Prop := x ∈ A

end TruthCore.Logic.LimitAdmission
