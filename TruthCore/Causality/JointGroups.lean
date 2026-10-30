import TruthCore.Causality.SourceWitness
import TruthCore.Causality.PluralRootConfluence

/-! Analyst semantics for #733, not a source-derived account of causation.
Groups index records, not additional substances. Membership projection reuses
Graph; its arrows never assert individual sufficiency. See the linked semantic
and source audit in docs/notes/joint-causal-groups-733.md. -/
namespace TruthCore.Causality.JointGroups
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.WorldSourceRegress

structure Groups (Event Group : Type) where
  contributors : Group → Set Event
  enablers : Group → Set Event
  effect : Group → Event
  admitted : Group → Prop

variable {E G B S : Type}

def Groups.members (h : Groups E G) (g : G) : Set E :=
  h.contributors g ∪ h.enablers g

def Groups.graph (h : Groups E G) : Graph E :=
  ⟨fun y x => ∃ g, h.admitted g ∧ h.effect g = x ∧ y ∈ h.members g⟩

/-- Events and their concrete bearers have different types; several events
may have the same bearer. Scenario variation is supplied, not inferred from
membership. Exercised is separate from both admission and sufficiency. -/
structure Exercise (Bearer Event Group Scenario : Type) where
  groups : Groups Event Group
  bearer : Event → Bearer
  occurs : Scenario → Event → Prop
  allowed : Scenario → Prop
  actual : Scenario
  exercised : Group → Prop

/-- Joint sufficiency relative to the entire supplied scenario space, including
its background conditions. No causal direction follows just from this formula. -/
def Exercise.suffices (m : Exercise B E G S) (antecedents : Set E) (effect : E) : Prop :=
  ∀ s, m.allowed s → (∀ e ∈ antecedents, m.occurs s e) → m.occurs s effect

def Exercise.jointlySufficient (m : Exercise B E G S) (g : G) : Prop :=
  m.suffices (m.groups.members g) (m.groups.effect g)

/-- Indispensable RELATIVE TO THIS GROUP with all other contributors and
all enablers retained: deleting e leaves an admissible failure scenario. -/
def Exercise.indispensable (m : Exercise B E G S) (g : G) (e : E) : Prop :=
  e ∈ m.groups.contributors g ∧
    ¬ m.suffices ((m.groups.contributors g \ {e}) ∪ m.groups.enablers g) (m.groups.effect g)

def Exercise.redundant (m : Exercise B E G S) (g : G) (e : E) : Prop :=
  e ∈ m.groups.contributors g ∧
    m.suffices ((m.groups.contributors g \ {e}) ∪ m.groups.enablers g) (m.groups.effect g)

/-- A coherence constraint, not a definition of genuine exercise: admitted
exercised records have occurring members and effects in an allowed actual
scenario. It does not promote sufficiency or occurrence to causal exercise. -/
def Exercise.coherent (m : Exercise B E G S) : Prop :=
  m.allowed m.actual ∧ ∀ g, m.exercised g → m.groups.admitted g ∧
    (∀ e ∈ m.groups.members g, m.occurs m.actual e) ∧
    m.occurs m.actual (m.groups.effect g)

/-- Projection for actual causal-exercise records, rather than merely
admitted alternatives. Sufficiency still does not entail this predicate. -/
def Exercise.exercisedGroups (m : Exercise B E G S) : Groups E G :=
  { m.groups with admitted := fun g => m.groups.admitted g ∧ m.exercised g }

/-- Same existing actual-node subtype/graph machinery, here interpreted as
occurring EVENTS, not existence or conservation of substantial bearers. -/
def Exercise.ontic (m : Exercise B E G S) :
    TruthCore.German.Kant.CosmologicalInference.Ontic Unit E where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ => m.occurs m.actual
  Causes := fun _ => m.exercisedGroups.graph.edge

abbrev Exercise.actualGraph (m : Exercise B E G S) := WorldSourceRegress.actualGraph m.ontic ()

/-- Pure representation adapter: exactly one record per target HAVING a
predecessor. No group is assigned to graph sources, no sufficiency asserted. -/
def recorded {E : Type} (K : Graph E) : Groups E {x // ∃ y, K.edge y x} where
  contributors := fun g => {y | K.edge y g.val}
  enablers := fun _ => ∅
  effect := Subtype.val
  admitted := fun _ => True

/-- Empty records add no membership edges; their presence does not assert
uncaused existence or a sufficient ground for anything. -/
def emptyRecord : Groups Unit Unit where
  contributors := fun _ => ∅
  enablers := fun _ => ∅
  effect := fun _ => ()
  admitted := fun _ => True

def ancestry {E : Type} (K : Graph E) := Relation.TransGen K.edge

def minimalAncestor {E : Type} (K : Graph E) (x : E) : Prop :=
  ∃ s, FiniteCausalPath K.edge x s ∧ ∀ y, ¬ ancestry K y s

/-- Least in the reflexive finite-ancestry order, not just a unique source. -/
def least {E : Type} (K : Graph E) (s : E) : Prop :=
  ∀ x, Relation.ReflTransGen K.edge s x

/-- Owner illustrations are partial event records, not empirical causal laws.
Electricity is a supply occurrence; air/fuel are availability events, and
spark/fire are effect occurrences. The bearer map does not reify groups. -/
inductive IgnitionEvent | supply | air | fuel | spark | fire deriving DecidableEq
inductive IgnitionBearer | supplyDevice | airBody | fuelBody | discharge | flame
inductive IgnitionGroup | spark | fire

def ignitionBearer : IgnitionEvent → IgnitionBearer
  | .supply => .supplyDevice | .air => .airBody | .fuel => .fuelBody
  | .spark => .discharge | .fire => .flame

def ignition : Groups IgnitionEvent IgnitionGroup where
  contributors := fun g => {e | match g with
    | .spark => e = .supply
    | .fire => e = .spark ∨ e = .fuel}
  enablers := fun _ => {e | e = .air}
  effect := fun g => match g with | .spark => .spark | .fire => .fire
  admitted := fun _ => True

/-- The illustration records have the proposed joint antecedents while
retaining contributor/enabler roles. No sufficiency field is present. -/
def IllustrationControls : Prop :=
  ignition.members .spark = {IgnitionEvent.supply, IgnitionEvent.air} ∧
  ignition.members .fire = {IgnitionEvent.spark, IgnitionEvent.air, IgnitionEvent.fuel} ∧
  IgnitionEvent.air ∉ ignition.contributors .spark ∧
  IgnitionEvent.air ∈ ignition.enablers .spark

/-- Finite cooperative fixture: effect = a AND (b OR c), with a separate
required enabling condition. It is a stipulation, not a combustion claim. -/
inductive Event | a | b | c | enabled | outcome deriving DecidableEq
inductive Group | ab | ac | abc deriving DecidableEq
abbrev Scenario := Bool × Bool × Bool × Bool

def fixtureGroups : Groups Event Group where
  contributors := fun g => {e | match g with
    | .ab => e = .a ∨ e = .b
    | .ac => e = .a ∨ e = .c
    | .abc => e = .a ∨ e = .b ∨ e = .c}
  enablers := fun _ => {e | e = .enabled}
  effect := fun _ => .outcome
  admitted := fun _ => True

def fixture : Exercise Unit Event Group Scenario where
  groups := fixtureGroups
  bearer := fun _ => ()
  occurs := fun (a,b,c,en) e => match e with
    | .a => a = true
    | .b => b = true
    | .c => c = true
    | .enabled => en = true
    | .outcome => a = true ∧ (b = true ∨ c = true) ∧ en = true
  allowed := fun _ => True
  actual := (true,true,true,true)
  exercised := fun _ => True

/-- Cooperative sufficiency, alternative sufficient groups, redundant c in
abc, relative indispensability, and the enabling-condition omission control.
No claim of full explanatory completeness is encoded. -/
def CooperationControls : Prop :=
  fixture.coherent ∧
  fixture.jointlySufficient .ab ∧ fixture.jointlySufficient .ac ∧
  fixture.jointlySufficient .abc ∧
  ¬ fixture.suffices {Event.a, Event.enabled} .outcome ∧
  ¬ fixture.suffices {Event.b, Event.enabled} .outcome ∧
  fixture.indispensable .ab .a ∧ fixture.indispensable .ab .b ∧
  fixture.redundant .abc .c ∧
  ¬ fixture.suffices {Event.a, Event.b} .outcome ∧
  Group.ab ≠ .ac

/-- Conditional order schema, including actual-domain population rather than
candidate-carrier inhabitance. Each event x already populates its own cone. -/
def OrderSchema : Prop :=
  (∀ (E G : Type) (h : Groups E G), h.graph.NoCycles →
    IsStrictOrder E (ancestry h.graph)) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S),
    WellFounded m.actualGraph.edge → ∀ x, minimalAncestor m.actualGraph x) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S),
    WellFounded m.actualGraph.edge → Nonempty (Actual m.ontic ()) →
      ∃ s, m.actualGraph.Source s) ∧
  (∀ (E : Type) (K : Graph E), K.NoCycles → ∀ s,
    least K s ↔ K.Source s ∧ ∀ x, FiniteCausalPath K.edge x s)

/-- The unchanged #634 interpretation, now also represented by one recorded
group at each caused node; its exact membership graph is preserved. -/
def RecordedOverlap : Prop :=
  (recorded (actualGraph overlap ())).graph = actualGraph overlap () ∧
  (∀ (g h : {x : Actual overlap () // ∃ y, (actualGraph overlap ()).edge y x}),
    (recorded (actualGraph overlap ())).effect g =
      (recorded (actualGraph overlap ())).effect h → g = h) ∧
  (∀ n, (recorded (actualGraph overlap ())).contributors
    ⟨⟨some n, True.intro⟩, ⟨⟨none, True.intro⟩, True.intro⟩⟩ =
      {y | y.val = none ∨ y.val = some (n + 1)}) ∧
  SourceWitness.ConfluentOverlapControl

/-- Reuse #707 as graph evidence only; jointControl does not mean cooperative
causal sufficiency. Two globally minimal sources refute a least element. -/
def PluralMinima : Prop :=
  PluralRootConfluence.Control ∧
  (∀ y, ¬ ancestry PluralRootConfluence.graph y (PluralRootConfluence.node .left)) ∧
  (∀ y, ¬ ancestry PluralRootConfluence.graph y (PluralRootConfluence.node .right)) ∧
  ¬ ∃ s, least PluralRootConfluence.graph s

/-- An admitted empty record without any actual event. This explicitly
prevents inferring uncaused existence from an empty membership set. -/
def absentEmpty : Exercise Unit Unit Unit Unit where
  groups := emptyRecord
  bearer := fun _ => ()
  occurs := fun _ _ => False
  allowed := fun _ => True
  actual := ()
  exercised := fun _ => False

/-- Omitting exercise, actual population, or nonempty membership cannot be
repaired by a sufficient-group record. Cycles remain possible as data. -/
def OmissionControls : Prop :=
  (let m := { fixture with exercised := fun _ => False };
    m.coherent ∧ m.jointlySufficient .ab ∧ ¬ m.exercised .ab) ∧
  (let m := { fixture with occurs := fun _ _ => False, exercised := fun _ => False };
    Nonempty Event ∧ ¬ Nonempty (Actual m.ontic ())) ∧
  (emptyRecord.admitted () ∧ emptyRecord.graph.Source () ∧
    ¬ Nonempty (Actual absentEmpty.ontic ())) ∧
  (let loop : Graph Unit := ⟨fun _ _ => True⟩;
    ¬ IsStrictOrder Unit (ancestry loop))

def Certificate : Prop := OrderSchema ∧ IllustrationControls ∧ CooperationControls ∧
  RecordedOverlap ∧ PluralMinima ∧ OmissionControls
end TruthCore.Causality.JointGroups
