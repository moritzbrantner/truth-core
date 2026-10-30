import TruthCore.Causality.JointGroups
import TruthCore.Causality.TemporalActualization

/-! Analyst-defined supply test for #734. Borrowing itself is not defined by
termination. Supply is an explicitly INDUCTIVE proposed explanatory standard,
not actual power. It differs from existential FinitelyGroundedPower and from
epistemic GeneratedWarrant: its rules are exercised causal-group records.
Its possibly infinite contributor sets impose no finite branching or uniform depth.
Enablers need occurrence via Exercise.coherent, not productive Supply.
Actual applicability and productive adequacy remain OPEN; see the linked note. -/
namespace TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.Causality.JointGroups
open TruthCore.Causality.WorldSourceRegress
variable {E G : Type}

/-- Intrinsic means an independently supplied, underived contribution in the
selected exercise context; it is not defined as graph sourcehood. -/
inductive Supply (h : Groups E G) (intrinsic : E → Prop) : E → Prop where
  | intrinsic (e) : intrinsic e → Supply h intrinsic e
  | joint (g) : h.admitted g → (∀ e ∈ h.contributors g, Supply h intrinsic e) →
      Supply h intrinsic (h.effect g)

/-- Local joint transmission, without selecting an inductive/coinductive
solution. `h` is the exercised-group restriction when used for actual exercise.
Actual power is independent of event occurrence in the general schema. -/
def LocalPower (h : Groups E G) (intrinsic active : E → Prop) : Prop :=
  ∀ e, active e ↔ intrinsic e ∨ ∃ g, h.admitted g ∧ h.effect g = e ∧
    ∀ a ∈ h.contributors g, active a

/-- A borrowing trap has no intrinsic member and every permitted alternative
for a target in D still requires some member of D. The required member may
vary with the group; a common source outside D does not remove the trap. -/
def Trap (h : Groups E G) (intrinsic : E → Prop) (D : Set E) : Prop :=
  (∀ e ∈ D, ¬ intrinsic e) ∧
  ∀ g, h.admitted g → h.effect g ∈ D → ∃ e ∈ h.contributors g, e ∈ D

/-- Proposed no-self-contained-borrowing principle: each nonempty set of
active contributions contains an intrinsic contribution or an admitted
alternative whose ENTIRE contributor set escapes it. This is an OPEN metaphysical
premise, not a consequence of coherence or scenario sufficiency. -/
def Escape (h : Groups E G) (intrinsic active : E → Prop) : Prop :=
  ∀ D : Set E, D ⊆ {e | active e} → D.Nonempty →
    (∃ e ∈ D, intrinsic e) ∨
    ∃ g, h.admitted g ∧ h.effect g ∈ D ∧ ∀ e ∈ h.contributors g, e ∉ D

/-- Active target records have active contributors. This is separate from
LocalPower, whose existential alternative alone cannot justify it. -/
def PoweredGroups (h : Groups E G) (A : E → Prop) : Prop :=
  ∀ g, h.admitted g → A (h.effect g) → ∀ e ∈ h.contributors g, A e

def Schema : Prop :=
  (∀ (E G : Type) (h : Groups E G) (I : E → Prop) (D : Set E),
    Trap h I D → ∀ e ∈ D, ¬ Supply h I e) ∧
  (∀ (E G : Type) (h : Groups E G) (I A : E → Prop),
    LocalPower h I A → PoweredGroups h A →
      ((∀ e, A e → Supply h I e) ↔ Escape h I A)) ∧
  (∀ (E G : Type) (h : Groups E G) (I : E → Prop),
    (∀ g, h.admitted g → (h.contributors g).Nonempty) →
    ∀ e, Supply h I e → ∃ s, FiniteCausalPath h.graph.edge e s ∧ I s)

abbrev Node := Actual overlap ()
def node (x : Option Nat) : Node := ⟨x, trivial⟩
abbrev K := actualGraph overlap ()
abbrev H := recorded K
def intrinsic (x : Node) : Prop := x.val = none
def branch : Set Node := {x | ∃ n, x.val = some n}
def group (n : Nat) : {x : Node // ∃ y, K.edge y x} :=
  ⟨node (some n), ⟨node none, trivial⟩⟩

/-- Both chain-on and chain-off retain the SAME intrinsic source. All groups
are exercised at the on scenario; scenario sufficiency is tested over BOTH.
The source and infinitely many derivative events are separate event tokens,
with bearer map id. A single exercise time/respect is held fixed externally. -/
def rooted : Exercise Node Node {x : Node // ∃ y, K.edge y x} Bool where
  groups := H
  bearer := id
  occurs := fun s e => intrinsic e ∨ s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

/-- The strongest selected rival restricts allowed scenarios to the on
history; it adds no intrinsic contribution and changes no joint membership.
Unique allowed history is selection, not a supply derivation. -/
def selected := { rooted with allowed := fun s => s = true }

def RootedControl : Prop :=
  H.graph = K ∧ SourceWitness.ConfluentOverlapControl ∧
  (∀ e : Node, e ∈ (H.graph.transmission intrinsic).lfp) ∧
  Supply H intrinsic (node none) ∧
  (∀ n, ¬ Supply H intrinsic (node (some n))) ∧
  (∀ g, node none ∈ H.members g) ∧
  rooted.coherent ∧ (∀ g, rooted.jointlySufficient g) ∧
  (∀ s, LocalPower H intrinsic (rooted.occurs s)) ∧
  (∀ n, rooted.indispensable (group n) (node (some (n + 1)))) ∧
  selected.coherent ∧ (∀ g, selected.jointlySufficient g) ∧
  (∀ s, selected.allowed s ↔ s = selected.actual) ∧
  ¬ Escape H intrinsic (rooted.occurs rooted.actual)

/-- A finite intrinsic actualizer/instrument and a source-free simultaneous
sustaining circle. The latter reuses #711's exact alternating-respect relation;
its local physical-motion compatibility does not establish sustaining supply. -/
def finite : Groups Bool Unit where
  contributors := fun _ => {false}
  enablers := fun _ => ∅
  effect := fun _ => true
  admitted := fun _ => True

def circle : Groups Bool Bool where
  contributors := fun g => {e | TemporalActualization.circleC e g}
  enablers := fun _ => ∅
  effect := id
  admitted := fun _ => True

/-- Omissions isolate the trap premises: allowing an intrinsic member or an
escaping alternative permits supply; an empty record can seed supply without
an intrinsic contribution. Nonempty-member premise in source extraction is
therefore necessary. No actual supply principle is asserted. -/
def Controls : Prop :=
  (Supply finite (fun e => e = false) true ∧
    LocalPower finite (fun e => e = false) (fun _ => True) ∧
    Escape finite (fun e => e = false) (fun _ => True)) ∧
  (TemporalActualization.Controls ∧
    LocalPower circle (fun _ => False) (fun _ => True) ∧
    (∀ e, ¬ Supply circle (fun _ => False) e)) ∧
  (Supply circle (fun _ => True) false) ∧
  (Supply {circle with contributors := fun _ => ∅} (fun _ => False) false) ∧
  (Supply emptyRecord (fun _ => False) ())

/-- Enabling availability at the exercise context is not productive supply. -/
def enabled : Groups (Fin 3) Unit where
  contributors := fun _ => {0}
  enablers := fun _ => {2}
  effect := fun _ => 1
  admitted := fun _ => True

def enabledExercise : Exercise (Fin 3) (Fin 3) Unit Unit where
  groups := enabled
  bearer := id
  occurs := fun _ _ => True
  allowed := fun _ => True
  actual := ()
  exercised := fun _ => True

def EnablerControl : Prop :=
  enabledExercise.coherent ∧
  Supply enabled (fun e => e = 0) 1 ∧
  (2 : Fin 3) ∈ enabled.enablers () ∧
  ¬ Supply enabled (fun e => e = 0) 2

/-- Two admitted alternatives for true: a self-sustaining record and an
external false-event record. Only admission is represented here; treating
both as exercised active suppliers is the tested mistake. -/
def alternatives : Groups Bool Bool where
  contributors := fun g => {if g then false else true}
  enablers := fun _ => ∅
  effect := fun _ => true
  admitted := fun _ => True

def AdmissionOmission : Prop :=
  LocalPower alternatives (fun _ => False) (fun e => e = true) ∧
  Escape alternatives (fun _ => False) (fun e => e = true) ∧
  ¬ Supply alternatives (fun _ => False) true ∧
  ¬ PoweredGroups alternatives (fun e => e = true) ∧
  Supply alternatives (fun e => e = false) true

def LegacyControls : Prop := EssentialPowerUnderdetermined ∧
  LocalObservationSelectsSolution ∧ FiniteGroundingNotClosedUnderEscapingSourceLimit

/-- Contributor power events and their effect belong to ONE selected exercise
instant/respect. Enablers occur under Exercise.coherent; they need not exercise
productive power in this respect. This does not identify events with bearers. -/
def AtContext {T R : Type} (h : Groups E G) (clock : E → T) (respect : E → R)
    (t : T) (r : R) : Prop :=
  ∀ g, h.admitted g → clock (h.effect g) = t ∧ respect (h.effect g) = r ∧
    ∀ e ∈ h.contributors g, clock e = t ∧ respect e = r

/-- A genuine two-contributor all-borrowed control. n+1 AND n+2 are required
by the local equation. The all-on/off scenarios are constraints, not production. -/
def unrootedGroups : Groups Nat Nat where
  contributors := fun n => {n + 1, n + 2}
  enablers := fun _ => ∅
  effect := id
  admitted := fun _ => True

def unrooted : Exercise Nat Nat Nat Bool where
  groups := unrootedGroups
  bearer := id
  occurs := fun s _ => s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

def SourceFreeControl : Prop :=
  unrooted.coherent ∧ (∀ g, unrooted.jointlySufficient g) ∧
  (∀ s, LocalPower unrootedGroups (fun _ => False) (unrooted.occurs s)) ∧
  (∀ e, ¬ Supply unrootedGroups (fun _ => False) e) ∧
  (∀ e, ¬ unrootedGroups.graph.Source e)

def ContextControls : Prop :=
  AtContext finite (fun _ => ()) (fun _ => ()) () () ∧
  AtContext unrootedGroups (fun _ => ()) (fun _ => ()) () () ∧
  AtContext H (fun _ => ()) (fun _ => ()) () ()

/-- Revised claim: contributor supply, explicit powered-group coherence,
and separate enabling occurrence; no real-world bridge is established. -/
def Certificate : Prop := Schema ∧ RootedControl ∧ Controls ∧ EnablerControl ∧
  AdmissionOmission ∧ LegacyControls ∧ SourceFreeControl ∧ ContextControls
end TruthCore.Causality.DerivativeJointPower
