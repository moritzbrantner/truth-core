import TruthCore.Explanation.UltimateAdequacy
import TruthCore.Explanation.PSRStrength
import Mathlib.Combinatorics.Quiver.ConnectedComponent

/-! Analyst comparison for #752 under the #733/#734 joint-group profile. It asks
what passes from a causal-group record to its projected membership graph and to
Mathlib's strongly connected components of that graph. `Supply` stays the #734
proposed inductive standard: nothing here defends it as actual productive
explanation, and a rival who rejects it is not refuted. A component is a
reachability class, not a substance, a cause or a ground. See
docs/notes/scc-sufficiency-752.md. -/
namespace TruthCore.Explanation.CondensationSufficiency
open TruthCore.Logic.Regress
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.PSRStrength

variable {E G B S : Type}

/-- The regress graph as a Mathlib quiver, one arrow per edge. -/
@[reducible] def quiverOf (K : Graph E) : Quiver E := ⟨fun y x => PLift (K.edge y x)⟩

/-- Mathlib's strongly connected components of a regress graph. -/
abbrev Comp (K : Graph E) := @Quiver.StronglyConnectedComponent E (quiverOf K)

def comp (K : Graph E) (e : E) : Comp K :=
  @Quiver.StronglyConnectedComponent.mk E (quiverOf K) e

/-- Mathlib's weakly connected component of a node. -/
def wcc (K : Graph E) (e : E) : @Quiver.WeaklyConnectedComponent E (quiverOf K) :=
  @Quiver.WeaklyConnectedComponent.mk E (quiverOf K) e

/-- Condensation: an edge between distinct components having some edge between
their members. Internal edges, and with them which members they joined, vanish. -/
def condensed (K : Graph E) : Graph (Comp K) :=
  ⟨fun A C => A ≠ C ∧ ∃ y x, comp K y = A ∧ comp K x = C ∧ K.edge y x⟩

/-- Condense each record of a membership graph: members become their components
and any member in the effect's own component is dropped. -/
def condenseGroups (h : Groups E G) : Groups (Comp h.graph) G where
  contributors := fun g => comp h.graph '' h.contributors g \ {comp h.graph (h.effect g)}
  enablers := fun g => comp h.graph '' h.enablers g \ {comp h.graph (h.effect g)}
  effect := fun g => comp h.graph (h.effect g)
  admitted := h.admitted

/-- A component counts as intrinsic when some member is intrinsic. -/
def condensedIntrinsic (K : Graph E) (I : E → Prop) (C : Comp K) : Prop :=
  ∃ e, comp K e = C ∧ I e

/-- `Escape` restricted to active subsets lying inside one component. -/
def ComponentEscape (h : Groups E G) (I A : E → Prop) : Prop :=
  ∀ (C : Comp h.graph) (D : Set E), D ⊆ {e | A e ∧ comp h.graph e = C} → D.Nonempty →
    (∃ e ∈ D, I e) ∨
    ∃ g, h.admitted g ∧ h.effect g ∈ D ∧ ∀ e ∈ h.contributors g, e ∉ D

/-- A cut visible in the projected graph alone: no intrinsic member and no
incoming edge from outside. `Trap` instead inspects whole records. -/
def GraphCut (K : Graph E) (I : E → Prop) (D : Set E) : Prop :=
  (∀ e ∈ D, ¬ I e) ∧ ∀ y x, x ∈ D → K.edge y x → y ∈ D

/-- Graph facts about condensation alone, for every graph. Only the
well-foundedness clause assumes a finite carrier. Sources pass to the
condensation; `CycleControl` shows the converse fails. -/
def GraphInvariants : Prop :=
  (∀ (E : Type) (K : Graph E), (condensed K).NoCycles) ∧
  (∀ (E : Type) (K : Graph E) (y x : E), Relation.ReflTransGen K.edge y x ↔
    Relation.ReflTransGen (condensed K).edge (comp K y) (comp K x)) ∧
  (∀ (E : Type) (K : Graph E) (y x : E), wcc K y = wcc K x ↔
    wcc (condensed K) (comp K y) = wcc (condensed K) (comp K x)) ∧
  (∀ (E : Type) (K : Graph E) (s : E), least K s ↔ least (condensed K) (comp K s)) ∧
  (∀ (E : Type) (K : Graph E) (s : E), K.Source s → (condensed K).Source (comp K s)) ∧
  (∀ (E : Type), Finite E → ∀ K : Graph E, WellFounded (condensed K).edge) ∧
  (∀ (E G : Type) (h : Groups E G), (condenseGroups h).graph = condensed h.graph)

/-- Each clause under its own hypotheses: Supply passes to the condensation;
over a well-founded condensation `Escape` and `ComponentEscape` coincide; under
LocalPower and PoweredGroups they then decide Supply of every active event, and
a finite carrier gives that well-foundedness; LocalPower with an acyclic
membership graph gives `ComponentEscape`; LocalPower with a well-founded
membership graph gives Supply of every active event; a graph cut with nonempty
contributor sets is a `Trap`. No clause applies these schemas to actual causes. -/
def SupplySchema : Prop :=
  (∀ (E G : Type) (h : Groups E G) (I : E → Prop) (e : E), Supply h I e →
    Supply (condenseGroups h) (condensedIntrinsic h.graph I) (comp h.graph e)) ∧
  (∀ (E G : Type) (h : Groups E G) (I A : E → Prop),
    WellFounded (condensed h.graph).edge → (Escape h I A ↔ ComponentEscape h I A)) ∧
  (∀ (E G : Type) (h : Groups E G) (I A : E → Prop),
    LocalPower h I A → PoweredGroups h A → WellFounded (condensed h.graph).edge →
      ((∀ e, A e → Supply h I e) ↔ ComponentEscape h I A)) ∧
  (∀ (E G : Type), Finite E → ∀ (h : Groups E G) (I A : E → Prop),
    LocalPower h I A → PoweredGroups h A →
      ((∀ e, A e → Supply h I e) ↔ ComponentEscape h I A)) ∧
  (∀ (E G : Type) (h : Groups E G) (I A : E → Prop),
    LocalPower h I A → h.graph.NoCycles → ComponentEscape h I A) ∧
  (∀ (E G : Type) (h : Groups E G) (I A : E → Prop),
    LocalPower h I A → WellFounded h.graph.edge → ∀ e, A e → Supply h I e) ∧
  (∀ (E G : Type) (h : Groups E G) (I : E → Prop) (D : Set E),
    (∀ g, h.admitted g → (h.contributors g).Nonempty) →
      GraphCut h.graph I D → Trap h I D)

/-! ## One projected graph, three record structures -/

inductive Ev | s | t | u deriving DecidableEq

/-- s → t, u → t, t → u: a source feeding a two-event cycle. -/
def pairGraph : Graph Ev :=
  ⟨fun y x => (y = .s ∧ x = .t) ∨ (y = .u ∧ x = .t) ∨ (y = .t ∧ x = .u)⟩

/-- t needs s AND u; u needs t. Index `true` is the record of t. -/
def conj : Groups Ev Bool where
  contributors := fun g => {e | if g then e = .s ∨ e = .u else e = .t}
  enablers := fun _ => ∅
  effect := fun g => if g then .t else .u
  admitted := fun _ => True

inductive DisjGroup | fromS | fromU | fromT

/-- t has two separate one-contributor records; u needs t. -/
def disj : Groups Ev DisjGroup where
  contributors := fun g => {e | match g with
    | .fromS => e = .s
    | .fromU => e = .u
    | .fromT => e = .t}
  enablers := fun _ => ∅
  effect := fun g => match g with
    | .fromT => .u
    | _ => .t
  admitted := fun _ => True

/-- As `conj`, except u is an enabler of t rather than a contributor. -/
def enabling : Groups Ev Bool where
  contributors := fun g => {e | if g then e = .s else e = .t}
  enablers := fun g => {e | g = true ∧ e = .u}
  effect := fun g => if g then .t else .u
  admitted := fun _ => True

/-- `conj` with the contributor u of t deleted from its record. -/
def pruned : Groups Ev Bool where
  contributors := fun g => {e | if g then e = .s else e = .t}
  enablers := fun _ => ∅
  effect := fun g => if g then .t else .u
  admitted := fun _ => True

def isS (e : Ev) : Prop := e = .s

/-- Shared exercise data: s occurs in both scenarios, t and u at `true` only,
and every record is exercised. Only the records and allowed scenarios vary. -/
def onOff {G : Type} (h : Groups Ev G) (allowed : Bool → Prop) : Exercise Ev Ev G Bool where
  groups := h
  bearer := id
  occurs := fun b e => e = .s ∨ b = true
  allowed := allowed
  actual := true
  exercised := fun _ => True

def everyScenario (_ : Bool) : Prop := True
def onScenario (b : Bool) : Prop := b = true
def allOn (_ : Ev) : Prop := True

/-- The set of the two cycle events. -/
def cycleEvents : Set Ev := {e | e = .t ∨ e = .u}

/-- Same projected graph, components and source; condensation has exactly two
components with an edge from `comp s` to `comp t`. -/
def PairSummary : Prop :=
  conj.graph = pairGraph ∧ disj.graph = pairGraph ∧ enabling.graph = pairGraph ∧
  comp pairGraph .t = comp pairGraph .u ∧ comp pairGraph .s ≠ comp pairGraph .t ∧
  (∀ e, wcc pairGraph e = wcc pairGraph .s) ∧
  (∀ e, pairGraph.Source e ↔ e = .s) ∧
  least pairGraph .s ∧ least (condensed pairGraph) (comp pairGraph .s) ∧
  (∀ C, C = comp pairGraph .s ∨ C = comp pairGraph .t) ∧
  (condensed pairGraph).edge (comp pairGraph .s) (comp pairGraph .t) ∧
  WellFounded (condensed pairGraph).edge

/-- The two exercises agree on bearers, occurrence, allowed scenarios, actual
scenario, exercise and actual graph, and differ in records and in Supply of t. -/
def SupplySplit : Prop :=
  (onOff conj onScenario).actualGraph = (onOff disj onScenario).actualGraph ∧
  (onOff conj onScenario).coherent ∧ (∀ g, (onOff conj onScenario).jointlySufficient g) ∧
  (onOff disj onScenario).coherent ∧ (∀ g, (onOff disj onScenario).jointlySufficient g) ∧
  LocalPower conj isS allOn ∧ PoweredGroups conj allOn ∧
  LocalPower disj isS allOn ∧ PoweredGroups disj allOn ∧
  Supply conj isS .s ∧ ¬ Supply conj isS .t ∧ ¬ Supply conj isS .u ∧
  (∀ e, Supply disj isS e) ∧
  (∀ e, Supply (condenseGroups conj) (condensedIntrinsic conj.graph isS) (comp conj.graph e)) ∧
  (∀ e, Supply (condenseGroups disj) (condensedIntrinsic disj.graph isS) (comp disj.graph e)) ∧
  ¬ ComponentEscape conj isS allOn ∧ ComponentEscape disj isS allOn ∧
  ¬ ∃ F : Graph Ev → (Ev → Prop) → Ev → Prop,
    ∀ (G : Type) (h : Groups Ev G) (I : Ev → Prop) (e : Ev), F h.graph I e ↔ Supply h I e

/-- `Trap` is not visible in the projected graph, and it does not track scenario
indispensability: u is indispensable over both scenarios and redundant over the
on scenario alone, with the same records and no Supply of t in either. Deleting
u from the record gives Supply of t and u. The empty record is a graph cut and
no trap, so the nonempty-contributor hypothesis in `SupplySchema` cannot be dropped. -/
def CutComparison : Prop :=
  Trap conj isS cycleEvents ∧ ¬ Trap disj isS cycleEvents ∧
  ¬ GraphCut pairGraph isS cycleEvents ∧
  (onOff conj everyScenario).coherent ∧ (∀ g, (onOff conj everyScenario).jointlySufficient g) ∧
  (onOff conj everyScenario).indispensable true .u ∧
  (onOff conj onScenario).redundant true .u ∧
  Supply pruned isS .t ∧ Supply pruned isS .u ∧
  GraphCut emptyRecord.graph (fun _ => False) {()} ∧
  ¬ Trap emptyRecord (fun _ => False) {()}

/-- `enabling` differs from `conj` only in making u an enabler of t. It has the
same membership graph, whose cycle survives, but an acyclic contributor
projection and Supply of every event. `conj` and `disj` both keep a cycle in
their contributor projections. -/
def EnablerControl : Prop :=
  (onOff enabling everyScenario).coherent ∧
  (∀ g, (onOff enabling everyScenario).jointlySufficient g) ∧
  LocalPower enabling isS allOn ∧ PoweredGroups enabling allOn ∧
  ¬ enabling.graph.NoCycles ∧
  ({ enabling with enablers := fun _ => ∅ } : Groups Ev Bool).graph.NoCycles ∧
  (∀ e, Supply enabling isS e) ∧ ComponentEscape enabling isS allOn ∧
  ¬ ({ conj with enablers := fun _ => ∅ } : Groups Ev Bool).graph.NoCycles ∧
  ¬ ({ disj with enablers := fun _ => ∅ } : Groups Ev DisjGroup).graph.NoCycles

/-! ## Infinite and cyclic controls -/

/-- The exact #634 graph with separate one-contributor records for each
derivative event, against the two-contributor records of #734. -/
def disjOverlap : Groups Node (Nat × Bool) where
  contributors := fun g => {e | if g.2 then e = node none else e = node (some (g.1 + 1))}
  enablers := fun _ => ∅
  effect := fun g => node (some g.1)
  admitted := fun _ => True

/-- On one acyclic graph with a least node and a non-well-founded condensation,
the #734 records have `ComponentEscape` without `Escape` and the other records
have Supply of every event. So the well-foundedness hypothesis cannot be dropped
from the reduction, and it is not necessary for Supply of every event. -/
def RootedBranches : Prop :=
  H.graph = K ∧ disjOverlap.graph = K ∧ K.NoCycles ∧
  least K (node none) ∧ ¬ WellFounded (condensed K).edge ∧
  LocalPower H intrinsic (rooted.occurs rooted.actual) ∧
  PoweredGroups H (rooted.occurs rooted.actual) ∧
  ComponentEscape H intrinsic (rooted.occurs rooted.actual) ∧
  ¬ Escape H intrinsic (rooted.occurs rooted.actual) ∧
  (∀ n, ¬ Supply H intrinsic (node (some n))) ∧
  (∀ e, Supply disjOverlap intrinsic e) ∧
  Escape disjOverlap intrinsic (rooted.occurs rooted.actual)

/-- A source-free acyclic chain: `ComponentEscape` holds for the on-scenario
active set, while `Escape` and Supply of every event fail. -/
def SourceFreeChain : Prop :=
  unrootedGroups.graph.NoCycles ∧ (∀ e, ¬ unrootedGroups.graph.Source e) ∧
  ¬ WellFounded (condensed unrootedGroups.graph).edge ∧
  ComponentEscape unrootedGroups (fun _ => False) (unrooted.occurs true) ∧
  ¬ Escape unrootedGroups (fun _ => False) (unrooted.occurs true) ∧
  ∀ e, ¬ Supply unrootedGroups (fun _ => False) e

/-- Each `some n` has a record needing the source and itself, and a record
needing `some (n + 1)`. -/
def loopChain : Groups (Option Nat) (Nat × Bool) where
  contributors := fun g => {e | if g.2 then e = none ∨ e = some g.1 else e = some (g.1 + 1)}
  enablers := fun _ => ∅
  effect := fun g => some g.1
  admitted := fun _ => True

def isNone (e : Option Nat) : Prop := e = none

/-- LocalPower, PoweredGroups, `ComponentEscape` and condensed Supply of every
component together do not give Supply: condensed Supply cannot stand in for the
well-founded hypothesis of the reduction. -/
def LoopChainControl : Prop :=
  LocalPower loopChain isNone (fun _ => True) ∧ PoweredGroups loopChain (fun _ => True) ∧
  ComponentEscape loopChain isNone (fun _ => True) ∧
  (∀ e, Supply (condenseGroups loopChain) (condensedIntrinsic loopChain.graph isNone)
    (comp loopChain.graph e)) ∧
  (∀ n, ¬ Supply loopChain isNone (some n)) ∧
  ¬ WellFounded (condensed loopChain.graph).edge

/-- Record-reason reading of the #757 arena at one world: the reasons of a fact
are the contributors of an exercised admitted record with that effect. Each such
token is an analyst stipulation, not a defended explanation. -/
def recordArena (m : Exercise B E G S) : Arena Unit E E where
  ontic := m.ontic
  holds := fun _ e => m.occurs m.actual e
  exist := id
  explains := fun _ r f => ∃ g, m.exercised g ∧ m.groups.admitted g ∧
    m.groups.effect g = f ∧ r ∈ m.groups.contributors g
  conjunct := fun _ _ => False

def circleExercise : Exercise Bool Bool Bool Unit where
  groups := circle
  bearer := id
  occurs := fun _ _ => True
  allowed := fun _ => True
  actual := ()
  exercised := fun _ => True

/-- The two cycle events share a component, which is a source of the condensation,
while the graph has no source. With no intrinsic member, LocalPower and FactPSR
under the record-reason reading hold without Supply. The same records with one
intrinsic member give Supply. Conversely `disj` has Supply of every event and
fails FactPSR under that reading, since s has no record. -/
def CycleControl : Prop :=
  comp circle.graph false = comp circle.graph true ∧
  (∀ e, ¬ circle.graph.Source e) ∧
  (condensed circle.graph).Source (comp circle.graph false) ∧
  WellFounded (condensed circle.graph).edge ∧
  circleExercise.coherent ∧
  LocalPower circle (fun _ => False) (fun _ => True) ∧
  FactPSR (recordArena circleExercise) () ∧
  (∀ e, ¬ Supply circle (fun _ => False) e) ∧
  ¬ ComponentEscape circle (fun _ => False) (fun _ => True) ∧
  (∀ e, Supply circle (fun e => e = false) e) ∧
  ComponentEscape circle (fun e => e = false) (fun _ => True) ∧
  (∀ e, Supply disj isS e) ∧ ¬ FactPSR (recordArena (onOff disj onScenario)) ()

open TruthCore.Explanation.UltimateAdequacy in
/-- The #735 plural fixture: all Supply and a single weak component, with two
distinct source components and no least component. -/
def PluralControl : Prop :=
  (∀ e, Supply (groups .plural) (intrinsic .plural) e) ∧
  (∀ e, wcc (groups .plural).graph e = wcc (groups .plural).graph 0) ∧
  comp (groups .plural).graph 0 ≠ comp (groups .plural).graph 1 ∧
  (condensed (groups .plural).graph).Source (comp (groups .plural).graph 0) ∧
  (condensed (groups .plural).graph).Source (comp (groups .plural).graph 1) ∧
  ¬ ∃ C, least (condensed (groups .plural).graph) C

def Certificate : Prop :=
  GraphInvariants ∧ SupplySchema ∧ PairSummary ∧ SupplySplit ∧ CutComparison ∧
  EnablerControl ∧ RootedBranches ∧ SourceFreeChain ∧ LoopChainControl ∧
  CycleControl ∧ PluralControl

end TruthCore.Explanation.CondensationSufficiency
