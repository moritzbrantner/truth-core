module
public import Mathlib.Data.Int.Order.Basic
public import Lean.Elab.Tactic.Omega

/-! Explicit analyst interpretations of the original accidental-series definition.
One profile fixes a causal task/respect and an observation time. `enabled` is
capacity for that task; an execution carries evidence of that capacity. This
state representation makes actual exercise imply capacity, not conversely.
Its applicability to real causes is OPEN, as is identification with the sourced
original. No accessibility or MovesAsMoved property is built into these states.

A historical edge may record generation OR replacement of an earlier instrument
by a later one. `completed` dates production or the relevant prior use, respectively.
Times have an arbitrary preorder; there is no first-time or well-foundedness axiom.
Intervention data give a removal time, presence, operating conditions and states.
Admissibility is a body: post-production/use, before observation, predecessor
absent, later member retained, and the later member's OTHER operating conditions
unchanged. Conditions and response states remain explicit primitive measurements,
not an 'adequate removal' flag. Their physical/causal applicability is OPEN.
Removing a currently necessary condition is deliberately a different test.
Neither nonemptiness nor response uniqueness is assumed. -/
@[expose] public section
namespace TruthCore.Causality.PerAccidensResponses

structure State where
  enabled : Bool
  execution : Option {_u : Unit // enabled = true}

def Capacity (s : State) : Prop := s.enabled = true
def Exercise (s : State) : Prop := s.execution.isSome = true

inductive Kind where
  | generation | instrument
  deriving DecidableEq

structure Profile (B T I C : Type) [Preorder T] where
  historical : Kind → B → B → Prop
  completed : B → T
  observation : T
  baseline : B → State
  present : B → Bool
  condition : B → C → Bool
  removed : I → B
  removalTime : I → T
  afterPresent : I → B → Bool
  afterCondition : I → B → C → Bool
  response : I → B → State

def Admissible {B T I C : Type} [Preorder T] (p : Profile B T I C)
    (y x : B) (i : I) : Prop :=
  p.completed y < p.completed x ∧ p.completed x < p.removalTime i ∧
  p.removalTime i ≤ p.observation ∧ p.removed i = y ∧
  p.afterPresent i y = false ∧ p.present x = true ∧ p.afterPresent i x = true ∧
  (∀ c, p.afterCondition i x c = p.condition x c)

def Available {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  ∀ k y x, p.historical k y x → ∃ i, Admissible p y x i

def AllCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  ∀ k y x, p.historical k y x → Exercise (p.baseline x) ∧
    ∀ i, Admissible p y x i → Capacity (p.response i x)

def SomeCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  ∀ k y x, p.historical k y x → Exercise (p.baseline x) ∧
    ∃ i, Admissible p y x i ∧ Capacity (p.response i x)

def AllExercise {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  ∀ k y x, p.historical k y x → Exercise (p.baseline x) ∧
    ∀ i, Admissible p y x i → Exercise (p.response i x)

def SomeExercise {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  ∀ k y x, p.historical k y x → Exercise (p.baseline x) ∧
    ∃ i, Admissible p y x i ∧ Exercise (p.response i x)

/-- Nonempty-domain versions used only for the two registered strength arrows.
These retain availability as a visible conjunct on BOTH ends. -/
def AvailableAllCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  Available p ∧ AllCapacity p
def AvailableSomeCapacity {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  Available p ∧ SomeCapacity p
def AvailableAllExercise {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  Available p ∧ AllExercise p
def AvailableSomeExercise {B T I C : Type} [Preorder T] (p : Profile B T I C) : Prop :=
  Available p ∧ SomeExercise p

def acting : State := ⟨true, some ⟨(), rfl⟩⟩
def ready : State := ⟨true, none⟩
def unable : State := ⟨false, none⟩

/-- Integer-dated no-first-history model. `none` is a separate present sustainer;
`some n` is produced/used at -n. BOTH edge kinds run some(n+1) -> some n.
Two responses per predecessor test universal versus existential survival.
The Boolean response selector changes exercise/capacity without changing the
retained member or the independently represented operating condition. This is
an abstract intervention structure, not a physical or metaphysical possibility proof. -/
def sample (good bad : State) : Profile (Option Nat) Int (Option Nat × Bool) Unit where
  historical := fun _ y x => ∃ n, y = some (n+1) ∧ x = some n
  completed := fun x => match x with | none => -2 | some n => -(n : Int)
  observation := 2
  baseline := fun _ => acting
  present := fun _ => true
  condition := fun _ _ => true
  removed := Prod.fst
  removalTime := fun _ => 1
  afterPresent := fun i x => decide (x ≠ i.1)
  afterCondition := fun i _ _ => decide (i.1 ≠ none)
  response := fun i _ => if i.1 = none then unable else if i.2 then good else bad

/-- Empty intervention carrier: universal survival is vacuous, existential is false. -/
def emptySample : Profile (Option Nat) Int Empty Unit where
  historical := (sample acting acting).historical
  completed := (sample acting acting).completed
  observation := 2
  baseline := fun _ => acting
  present := fun _ => true
  condition := fun _ _ => true
  removed := Empty.elim
  removalTime := Empty.elim
  afterPresent := Empty.elim
  afterCondition := Empty.elim
  response := Empty.elim

/-- Controls include all four cells, proper quantifier/strength distinctions,
empty-domain failure, both historical kinds, no first predecessor, and separate
current-condition removal. They assert only properties of these explicit models. -/
def Controls : Prop :=
  (Available (sample acting acting) ∧ AllExercise (sample acting acting)) ∧
  (AllCapacity (sample ready ready) ∧ ¬ SomeExercise (sample ready ready)) ∧
  (SomeExercise (sample acting unable) ∧ ¬ AllCapacity (sample acting unable)) ∧
  (AllExercise emptySample ∧ ¬ SomeCapacity emptySample ∧ ¬ Available emptySample) ∧
  (∀ k n, (sample acting acting).historical k (some (n+1)) (some n)) ∧
  (∀ n, ∃ y, (sample acting acting).historical .generation y (some n)) ∧
  ((sample acting acting).afterPresent (none, true) (some 0) = true ∧
    (sample acting acting).afterCondition (none, true) (some 0) () = false ∧
    ¬ Capacity ((sample acting acting).response (none, true) (some 0)) ∧
    ¬ Admissible (sample acting acting) none (some 0) (none, true))
end TruthCore.Causality.PerAccidensResponses
