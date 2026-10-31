import TruthCore.Explanation.JointCooperation
import TruthCore.Explanation.ExplanatoryAdequacy
import TruthCore.Explanation.CondensationSufficiency

/-! Analyst semantics for #745, not a source-derived account of explanation.
Reuses the #733 records, the #734 `Supply`, the #755 arena, the #750 `ReasonClosed`,
the #752 condensation and the #744 scenario labels. A stop predicate is an explicit
parameter, so no clause says where explanation may stop. Records stay interpreted
data: nothing here makes a record productive, and an analyst may list an idle event
as a member. No clause asserts that an account must be closed. Events carry the
demand; the existence of their bearers is not treated. A causal power enters only as
an event listed as a member of a record. See docs/notes/explanatory-closure-745.md. -/
namespace TruthCore.Explanation.ExplanatoryClosure
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCooperation
open TruthCore.German.Kant.CosmologicalInference

variable {B E G S : Type}

/-! ## Closure and its inductive form -/

/-- Every event of `A` stops or has one admitted record with all contributors and
enablers in `A`. One record suffices: other records of the same effect are ignored. -/
def Accounted (h : Groups E G) (Stop : E → Prop) (A : Set E) : Prop :=
  ∀ e ∈ A, Stop e ∨ ∃ g, h.admitted g ∧ h.effect g = e ∧ h.members g ⊆ A

/-- Some account of `e` is closed under this stop predicate. Cycles and infinite
descent are not excluded. -/
def Closed (h : Groups E G) (Stop : E → Prop) (e : E) : Prop :=
  ∃ A, e ∈ A ∧ Accounted h Stop A

/-- Enablers counted as contributors, so that #734's `Supply` demands them too. -/
def allMembers (h : Groups E G) : Groups E G :=
  { h with contributors := h.members, enablers := fun _ => ∅ }

/-- Inductive closure: `Supply` where every member is demanded. -/
def FullSupply (h : Groups E G) (Stop : E → Prop) (e : E) : Prop :=
  Supply (allMembers h) Stop e

/-- An infinite descent from `t` through `A`, stopping nowhere and with no member
having full supply: some walk member is its own ancestor, or the walk never repeats. -/
def Unfounded (h : Groups E G) (Stop : E → Prop) (A : Set E) (t : E) : Prop :=
  ∃ f : Nat → E, f 0 = t ∧
    (∀ n, f n ∈ A ∧ ¬ Stop (f n) ∧ ¬ FullSupply h Stop (f n) ∧ h.graph.edge (f (n + 1)) (f n)) ∧
    ((∃ i, ancestry h.graph (f i) (f i)) ∨ Function.Injective f)

/-! ## Reasons read from records, with scenarios as worlds -/

/-- The #755 arena of an exercise: worlds are scenarios, accessibility goes to the
allowed ones, and at the actual scenario the reasons of an effect are all members of
its exercised admitted records. This reason token is an analyst stipulation. It
differs from #752's `recordArena`, which has one world and contributors only. -/
def arena (m : Exercise B E G S) : Arena S E E where
  ontic := {
    frame := ⟨fun _ v => m.allowed v⟩
    ExistsAt := m.occurs
    Causes := fun s y x => s = m.actual ∧ m.exercisedGroups.graph.edge y x }
  holds := m.occurs
  exist := id
  explains := fun s r f => s = m.actual ∧ ∃ g, m.groups.admitted g ∧ m.exercised g ∧
    m.groups.effect g = f ∧ r ∈ m.groups.members g
  conjunct := fun _ _ => False

/-- A contingent event in the ancestry of `t`, itself included, with no exercised
record at all. -/
def BruteStop (m : Exercise B E G S) (t : E) : Prop :=
  ∃ x, Relation.ReflTransGen m.exercisedGroups.graph.edge x t ∧
    Contingent (arena m) m.actual x ∧
    ∀ g, m.groups.admitted g → m.exercised g → m.groups.effect g ≠ x

/-- An exercised record in the ancestry of `t`, itself included, that is not jointly
sufficient for its effect in this scenario space. -/
def IncompleteLink (m : Exercise B E G S) (t : E) : Prop :=
  ∃ g, m.groups.admitted g ∧ m.exercised g ∧ ¬ m.jointlySufficient g ∧
    Relation.ReflTransGen m.exercisedGroups.graph.edge (m.groups.effect g) t

/-- Member of a record whose deletion, with every other contributor and enabler
retained, leaves an allowed failure of the effect. Relative to one scenario space
and to the record's membership. -/
def IndispensableCondition (m : Exercise B E G S) (g : G) (e : E) : Prop :=
  e ∈ m.groups.members g ∧ ¬ m.suffices (m.groups.members g \ {e}) (m.groups.effect g)

/-- Closure demanding only the indispensable members of the chosen record. -/
def IndispensablyClosed (m : Exercise B E G S) (Stop : E → Prop) (e : E) : Prop :=
  ∃ A : Set E, e ∈ A ∧ ∀ x ∈ A, Stop x ∨ ∃ g, m.groups.admitted g ∧ m.exercised g ∧
    m.groups.effect g = x ∧ ∀ y, IndispensableCondition m g y → y ∈ A

/-! ## General statements -/

/-- Inductive closure gives closure and contributor `Supply`, on the same graph; it
coincides with `Supply` when no record has enablers. Failure of inductive closure is
exactly membership in a borrowing trap of `allMembers`. A well-founded membership
graph, or an acyclic one on a finite carrier, makes every member of an accounted set
inductively closed. -/
def Ladder : Prop :=
  ∀ (E G : Type) (h : Groups E G) (Stop : E → Prop),
    (allMembers h).graph = h.graph ∧
    (∀ e, FullSupply h Stop e → Closed h Stop e) ∧
    (∀ e, FullSupply h Stop e → Supply h Stop e) ∧
    ((∀ g, h.enablers g = ∅) → ∀ e, Supply h Stop e → FullSupply h Stop e) ∧
    (∀ e, ¬ FullSupply h Stop e ↔ ∃ D, Trap (allMembers h) Stop D ∧ e ∈ D) ∧
    (WellFounded h.graph.edge → ∀ e, Closed h Stop e → FullSupply h Stop e) ∧
    (Finite E → h.graph.NoCycles → ∀ e, Closed h Stop e → FullSupply h Stop e)

/-- Coverage for one member of one accounted set: inductive closure, or an infinite
descent with no full supply. The two exclude each other at `t`. Exclusivity of a cycle
and a nonrepeating walk across different walks is not claimed. -/
def Fork : Prop :=
  ∀ (E G : Type) (h : Groups E G) (Stop : E → Prop) (A : Set E) (t : E),
    Accounted h Stop A → t ∈ A → (FullSupply h Stop t ∨ Unfounded h Stop A t) ∧
      ¬ (FullSupply h Stop t ∧ Unfounded h Stop A t)

/-- In a coherent exercise whose exercised records have a member: closure of every
contingent event with stops at scenario necessity is equivalent to the contingent-fact
PSR of the record arena, and stop-free closure of every occurring event to its fact
PSR. Contingent-fact PSR gives closure of each occurring event. -/
def Collapse : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S), m.coherent →
    (∀ g, m.groups.admitted g → m.exercised g → (m.groups.members g).Nonempty) →
    ((∀ e, Contingent (arena m) m.actual e → Closed m.exercisedGroups (NecessaryIn m) e) ↔
      ContingentPSR (arena m) m.actual) ∧
    ((∀ e, m.occurs m.actual e → Closed m.exercisedGroups (fun _ => False) e) ↔
      FactPSR (arena m) m.actual) ∧
    (ContingentPSR (arena m) m.actual →
      ∀ e, m.occurs m.actual e → Closed m.exercisedGroups (NecessaryIn m) e)

/-- For a target that is not scenario-necessary and all of whose exercised records
list every other contingent event, with exercised records having a member, closure of
that one target gives contingent-fact PSR. This assumes no coherence. -/
def TotalTarget : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (t : E), ¬ NecessaryIn m t →
    (∀ g, m.groups.admitted g → m.exercised g → (m.groups.members g).Nonempty) →
    (∀ g, m.groups.admitted g → m.exercised g → m.groups.effect g = t →
      ∀ c, Contingent (arena m) m.actual c → c ≠ t → c ∈ m.groups.members g) →
    Closed m.exercisedGroups (NecessaryIn m) t → ContingentPSR (arena m) m.actual

/-- A #750 reason-closed account in the record arena is accounted with stops at
scenario necessity. The converse fails at `family .cycle`, in `Shapes`. -/
def ReasonBridge : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (A : E → Prop) (x : E),
    ExplanatoryAdequacy.ReasonClosed (arena m) m.actual A x →
    Closed m.exercisedGroups (NecessaryIn m) x

/-- Coverage for a contingent event of a coherent exercise, with stops at scenario
necessity: a contingent ancestor with no exercised record, an unfounded descent in
some accounted set, or an exercised ancestor record that is not jointly sufficient.
Branches may overlap; exclusivity is not claimed. -/
def Trilemma : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (t : E), m.coherent →
    Contingent (arena m) m.actual t →
    BruteStop m t ∨
    (∃ A, Accounted m.exercisedGroups (NecessaryIn m) A ∧
      Unfounded m.exercisedGroups (NecessaryIn m) A t) ∨
    IncompleteLink m t

/-- Inductive closure with stops occurring at every allowed scenario: if the target
does not occur at every allowed scenario, then an ancestor record is not jointly
sufficient; so if every exercised record is sufficient the target occurs at every
allowed scenario. -/
def LinkCost : Prop :=
  ∀ (B E G S : Type) (m : Exercise B E G S) (Stop : E → Prop) (t : E),
    FullSupply m.exercisedGroups Stop t → (∀ e, Stop e → NecessaryIn m e) →
    (¬ NecessaryIn m t → IncompleteLink m t) ∧
    ((∀ g, m.groups.admitted g → m.exercised g → m.jointlySufficient g) → NecessaryIn m t)

/-- `LinkCost` for stops necessary at a world and a target contingent there, with
every allowed scenario matching an accessible world and conversely. -/
def ModalCost : Prop :=
  ∀ (B E G S W : Type) (m : Exercise B E G S) (o : Ontic W E) (w : W) (Stop : E → Prop) (t : E),
    ScenariosAreWorlds m o w → WorldsAreScenarios m o w →
    FullSupply m.exercisedGroups Stop t → (∀ e, Stop e → NecessaryAt o w e) →
    ContingentAt o w t → IncompleteLink m t

/-! ## The joint group `{a, b, c}` with enabler `p`, under four record sets -/

inductive Ev | d | a | b | c | p | s | q | link (n : Nat)
inductive Gp | dg | sa | sb | sc | sp | qp | pq | lp | ll (n : Nat)
inductive Mode | bare | rooted | chain | cycle deriving DecidableEq

/-- `s` is a contributor for `a`, `b` and `c`, whatever the mode. The modes differ in
what, if anything, is recorded for the enabler `p`. -/
def familyGroups (mo : Mode) : Groups Ev Gp where
  contributors := fun g => {e | match g with
    | .dg => e = .a ∨ e = .b ∨ e = .c
    | .sa | .sb | .sc | .sp => e = .s
    | .qp => e = .p
    | .pq => e = .q
    | .lp => e = .link 0
    | .ll n => e = .link (n + 1)}
  enablers := fun g => {e | match g with
    | .dg => e = .p
    | _ => False}
  effect := fun g => match g with
    | .dg => .d
    | .sa => .a
    | .sb => .b
    | .sc => .c
    | .sp | .pq | .lp => .p
    | .qp => .q
    | .ll n => .link n
  admitted := fun g => match g with
    | .dg | .sa | .sb | .sc => True
    | .sp => mo = .rooted
    | .qp | .pq => mo = .cycle
    | .lp | .ll _ => mo = .chain

abbrev Scen := Bool × Bool × Bool × Bool

/-- `s` occurs at every scenario. Four bits set `a`, `b`, `c`, `p`, and `d` needs all
four. `q` occurs only in the cycle mode and the links only in the chain mode, with `p`. -/
def family (mo : Mode) : Exercise Ev Ev Gp Scen where
  groups := familyGroups mo
  bearer := id
  occurs := fun s e => match e with
    | .s => True
    | .a => s.1 = true
    | .b => s.2.1 = true
    | .c => s.2.2.1 = true
    | .p => s.2.2.2 = true
    | .d => s.1 = true ∧ s.2.1 = true ∧ s.2.2.1 = true ∧ s.2.2.2 = true
    | .q => mo = .cycle ∧ s.2.2.2 = true
    | .link _ => mo = .chain ∧ s.2.2.2 = true
  allowed := fun _ => True
  actual := (true, true, true, true)
  exercised := (familyGroups mo).admitted

/-- The `bare` records and occurrence table, restricted to the actual scenario. -/
def narrowBare : Exercise Ev Ev Gp Scen :=
  { family .bare with allowed := fun s => s = (true, true, true, true) }

open TruthCore.Explanation.CondensationSufficiency in
/-- All modes: the record `dg` is complete and its members are indispensable, and
`d` has contributor `Supply` from `s`; an ancestor record is incomplete in each.
`bare` and `rooted` have one occurrence table and differ in verdict. `bare` has
no closure with stops at scenario necessity, has it once `p` is added as a stop, and
has no contingent-fact PSR, though `a` is closed. `rooted` has inductive closure.
`chain` and `cycle` have contingent-fact PSR and closure of `d` without inductive
closure. In `cycle`, `p` and `q` share a component, whose condensed record `pq` has no
contributor left, so it has `Supply` with no intrinsic event; and no #750 reason-closed
account of `d` exists there. The same `bare` records restricted to the actual
scenario have closure and no indispensable `p`. -/
def Shapes : Prop :=
  (∀ mo, (family mo).coherent ∧ (family mo).jointlySufficient .dg ∧
    (family mo).indispensable .dg .a ∧ (family mo).indispensable .dg .b ∧
    (family mo).indispensable .dg .c ∧ IndispensableCondition (family mo) .dg .p ∧
    NecessaryIn (family mo) .s ∧
    Supply (family mo).exercisedGroups (fun e => e = .s) .d ∧
    IncompleteLink (family mo) .d) ∧
  ((family .bare).occurs = (family .rooted).occurs ∧
    (family .bare).allowed = (family .rooted).allowed ∧
    (family .bare).actual = (family .rooted).actual) ∧
  (¬ Closed (family .bare).exercisedGroups (NecessaryIn (family .bare)) .d ∧
    ¬ FullSupply (family .bare).exercisedGroups (fun e => e = .s) .d ∧
    FullSupply (family .bare).exercisedGroups (fun e => NecessaryIn (family .bare) e ∨ e = .p) .d ∧
    Closed (family .bare).exercisedGroups (NecessaryIn (family .bare)) .a ∧
    ¬ ContingentPSR (arena (family .bare)) (family .bare).actual ∧
    BruteStop (family .bare) .d) ∧
  (FullSupply (family .rooted).exercisedGroups (NecessaryIn (family .rooted)) .d ∧
    ContingentPSR (arena (family .rooted)) (family .rooted).actual) ∧
  (∀ mo, mo = .chain ∨ mo = .cycle →
    Closed (family mo).exercisedGroups (NecessaryIn (family mo)) .d ∧
    ¬ FullSupply (family mo).exercisedGroups (NecessaryIn (family mo)) .d ∧
    ContingentPSR (arena (family mo)) (family mo).actual) ∧
  (comp (familyGroups .cycle).graph .p = comp (familyGroups .cycle).graph .q ∧
    Supply (condenseGroups (familyGroups .cycle)) (fun _ => False)
      (comp (familyGroups .cycle).graph .p) ∧
    ∀ A, ¬ ExplanatoryAdequacy.ReasonClosed (arena (family .cycle)) (family .cycle).actual A .d) ∧
  (Closed narrowBare.exercisedGroups (NecessaryIn narrowBare) .d ∧
    ¬ IndispensableCondition narrowBare .dg .p) ∧
  -- the total-target hypothesis holds at `d` in both `bare` and `rooted`
  (∀ mo, mo = .bare ∨ mo = .rooted → ∀ g, (family mo).groups.admitted g →
    (family mo).groups.effect g = .d →
    ∀ k, Contingent (arena (family mo)) (family mo).actual k → k ≠ .d →
      k ∈ (family mo).groups.members g)

/-! ## Each trilemma horn alone, and one omission per member of the cost -/

inductive CEv | n | p | q | t | link (k : Nat)
inductive CGp | tp | tn | pq | qp | pl | ll (k : Nat)
inductive CMode | brute | source | cycle | chain deriving DecidableEq

def controlGroups (mo : CMode) : Groups CEv CGp where
  contributors := fun g => {e | match g with
    | .tp => e = .p
    | .tn => e = .n
    | .pq => e = .q
    | .qp => e = .p
    | .pl => e = .link 0
    | .ll k => e = .link (k + 1)}
  enablers := fun _ => ∅
  effect := fun g => match g with
    | .tp | .tn => .t
    | .pq | .pl => .p
    | .qp => .q
    | .ll k => .link k
  admitted := fun g => match g with
    | .tp => mo ≠ .source
    | .tn => mo = .source
    | .pq | .qp => mo = .cycle
    | .pl | .ll _ => mo = .chain

/-- `n` occurs at every scenario and every other event at `true` only. -/
def ctl (mo : CMode) : Exercise CEv CEv CGp Bool where
  groups := controlGroups mo
  bearer := id
  occurs := fun s e => match e with
    | .n => True
    | _ => s = true
  allowed := fun _ => True
  actual := true
  exercised := (controlGroups mo).admitted

/-- `source` restricted to the actual scenario. -/
def narrowSource : Exercise CEv CEv CGp Bool :=
  { ctl .source with allowed := fun s => s = true }

/-- Which horn each record set takes, with `t` contingent throughout, and the one
omission from the cost clause that each shows. In `brute` only the first horn holds
and the stop at `p` is not scenario-necessary. In `source` only the third holds,
with inductive closure at necessary stops. In `cycle` and `chain` only the second
holds, with closure and no incomplete ancestor record; `cycle` has a two-step cycle and
the graph of `chain` has none. In
`narrowSource` inductive closure and sufficiency hold and `t` occurs everywhere. -/
def TrilemmaControls : Prop :=
  (∀ mo, (ctl mo).coherent ∧ Contingent (arena (ctl mo)) (ctl mo).actual .t) ∧
  (BruteStop (ctl .brute) .t ∧
    (∀ A, ¬ Unfounded (ctl .brute).exercisedGroups (NecessaryIn (ctl .brute)) A .t) ∧
    ¬ IncompleteLink (ctl .brute) .t ∧
    FullSupply (ctl .brute).exercisedGroups (fun e => e = .p) .t ∧
    ¬ NecessaryIn (ctl .brute) .p) ∧
  (¬ BruteStop (ctl .source) .t ∧
    (∀ A, ¬ Unfounded (ctl .source).exercisedGroups (NecessaryIn (ctl .source)) A .t) ∧
    IncompleteLink (ctl .source) .t ∧
    FullSupply (ctl .source).exercisedGroups (NecessaryIn (ctl .source)) .t) ∧
  (∀ mo, mo = .cycle ∨ mo = .chain →
    ¬ BruteStop (ctl mo) .t ∧
    ¬ IncompleteLink (ctl mo) .t ∧
    Closed (ctl mo).exercisedGroups (NecessaryIn (ctl mo)) .t ∧
    ¬ FullSupply (ctl mo).exercisedGroups (NecessaryIn (ctl mo)) .t ∧
    (∃ A, Accounted (ctl mo).exercisedGroups (NecessaryIn (ctl mo)) A ∧
      Unfounded (ctl mo).exercisedGroups (NecessaryIn (ctl mo)) A .t)) ∧
  (ctl .cycle).exercisedGroups.graph.edge .p .q ∧
  (ctl .cycle).exercisedGroups.graph.edge .q .p ∧
  (ctl .chain).exercisedGroups.graph.NoCycles ∧
  (FullSupply narrowSource.exercisedGroups (NecessaryIn narrowSource) .t ∧
    (∀ g, narrowSource.groups.admitted g → narrowSource.exercised g →
      narrowSource.jointlySufficient g) ∧
    NecessaryIn narrowSource .t)

/-! ## The indispensable reading and the premises of `Collapse` -/

inductive OEv | x | y | z

/-- Two members, each alone sufficing for the effect, neither with a record. -/
def backup : Exercise OEv OEv Unit (Bool × Bool) where
  groups := {
    contributors := fun _ => {e | match e with
      | .x | .y => True
      | .z => False}
    enablers := fun _ => ∅
    effect := fun _ => .z
    admitted := fun _ => True }
  bearer := id
  occurs := fun s e => match e with
    | .x => s.1 = true
    | .y => s.2 = true
    | .z => s.1 = true ∨ s.2 = true
  allowed := fun _ => True
  actual := (true, true)
  exercised := fun _ => True

/-- Under joint sufficiency, a member occurring at every allowed scenario is not an
indispensable condition. For a contributor that is not also an enabler, the #733
notion and this one agree. Closure gives indispensable closure. At `z` in `backup`
indispensable closure holds and closure fails. -/
def IndispensableLens : Prop :=
  (∀ (B E G S : Type) (m : Exercise B E G S) (g : G) (e : E),
    m.jointlySufficient g → NecessaryIn m e → ¬ IndispensableCondition m g e) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (g : G) (e : E),
    e ∈ m.groups.contributors g → e ∉ m.groups.enablers g →
    (m.indispensable g e ↔ IndispensableCondition m g e)) ∧
  (∀ (B E G S : Type) (m : Exercise B E G S) (Stop : E → Prop) (e : E),
    Closed m.exercisedGroups Stop e → IndispensablyClosed m Stop e) ∧
  (backup.coherent ∧ backup.jointlySufficient () ∧
    IndispensablyClosed backup (NecessaryIn backup) .z ∧
    ¬ Closed backup.exercisedGroups (NecessaryIn backup) .z)

/-- A record with no member: the #733 empty record, with a contingent effect. -/
def emptyExercise : Exercise Unit Unit Unit Bool where
  groups := emptyRecord
  bearer := id
  occurs := fun s _ => s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

/-- `false` is listed as a member of the record of `true` and never occurs. -/
def incoherentExercise : Exercise Bool Bool Unit Bool where
  groups := {
    contributors := fun _ => {false}
    enablers := fun _ => ∅
    effect := fun _ => true
    admitted := fun _ => True }
  bearer := id
  occurs := fun s e => e = true ∧ s = true
  allowed := fun _ => True
  actual := true
  exercised := fun _ => True

/-- Omitting either premise of `Collapse` breaks one direction. -/
def PremiseControls : Prop :=
  (emptyExercise.coherent ∧
    (∀ e, Contingent (arena emptyExercise) emptyExercise.actual e →
      Closed emptyExercise.exercisedGroups (NecessaryIn emptyExercise) e) ∧
    ¬ ContingentPSR (arena emptyExercise) emptyExercise.actual) ∧
  (¬ incoherentExercise.coherent ∧
    (∀ g, incoherentExercise.groups.admitted g → incoherentExercise.exercised g →
      (incoherentExercise.groups.members g).Nonempty) ∧
    ContingentPSR (arena incoherentExercise) incoherentExercise.actual ∧
    Contingent (arena incoherentExercise) incoherentExercise.actual true ∧
    ¬ Closed incoherentExercise.exercisedGroups (NecessaryIn incoherentExercise) true)

/-- The checked map for #745. It does not assert that any explanation must be
closed, that any stop is legitimate, or that any record is productive. -/
def Certificate : Prop :=
  Ladder ∧ Fork ∧ Collapse ∧ TotalTarget ∧ ReasonBridge ∧ Trilemma ∧ LinkCost ∧ ModalCost ∧
  Shapes ∧ TrilemmaControls ∧ IndispensableLens ∧ PremiseControls

end TruthCore.Explanation.ExplanatoryClosure
