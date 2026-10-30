import TruthCore.Explanation.PSRStrength
import TruthCore.Explanation.UltimateAdequacy

/-!
# Local causal records and the actual complete history (#751)

Composes #467 populated histories, #736 selection, #733/#734 causal-group records
and the #755 reason arena under one question: why does this complete supplied
history obtain rather than an accessible rival? Worlds are analyst indices.
A model shows a formal bundle satisfiable, not metaphysically possible, and
accessibility is not real possibility. No world-selecting event is modelled, and
no theorem here defends the demand or refutes physicalism: it is left an explicit
parameter. See `docs/notes/actual-world-gap-751.md`.
-/
namespace TruthCore.Explanation.ActualWorldGap

open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive
open TruthCore.Explanation.HistorySelection TruthCore.Explanation.PSRStrength
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower

variable {W B T F : Type}

/-! ## Vocabulary -/

/-- The same supplied causal edges at both worlds. -/
def SameTable (h : History W B T) (v a : W) : Prop :=
  ∀ y x, h.ontic.Causes v y x ↔ h.ontic.Causes a y x

/-- Agreement on the complete supplied history: presence at every time and the
causal edges. It compares supplied presence and edges, not all qualitative facts. -/
def SameTotal (h : History W B T) (v a : W) : Prop :=
  SameHistory h v a ∧ SameTable h v a

/-- A history with a reason arena over the same ontic structure. `total a` is the
rigid fact that the complete history of `a` obtains: which world it is true at
does not depend on any designated index. No aggregate being is added. -/
structure Case (W B T F : Type) where
  history : History W B T
  holds : W → F → Prop
  exist : B → F
  explains : W → F → F → Prop
  conjunct : F → F → Prop
  total : W → F
  total_holds : ∀ a v, holds v (total a) ↔ SameTotal history v a

/-- The #755 arena of a case. -/
def Case.arena (c : Case W B T F) : Arena W B F :=
  ⟨c.history.ontic, c.holds, c.exist, c.explains, c.conjunct⟩

/-- An accessible world with a different supplied presence history. -/
def Rival (h : History W B T) (a b : W) : Prop :=
  h.ontic.frame.access a b ∧ ¬ SameHistory h b a

/-- Causal edges hold between existents. -/
def Sound (h : History W B T) (v : W) : Prop :=
  ∀ y x, h.ontic.Causes v y x → h.ontic.ExistsAt v y ∧ h.ontic.ExistsAt v x

/-- Every existent has an edge, as effect or as cause. A caused member and a source
with an effect both qualify; a causally idle existent does not. -/
def Recorded (h : History W B T) (v : W) : Prop :=
  ∀ x, h.ontic.ExistsAt v x → ∃ y, h.ontic.Causes v y x ∨ h.ontic.Causes v x y

/-- Existents are present at every supplied time, and only they are. -/
def Perpetual (h : History W B T) (v : W) : Prop :=
  ∀ x t, h.IsAt v x t ↔ h.ontic.ExistsAt v x

/-- The local conditions under which the edge table recovers presence. -/
def LocalRecord (h : History W B T) (v : W) : Prop :=
  Sound h v ∧ Recorded h v ∧ Perpetual h v

/-- The named edge table as a reason-vector for #736 selection. -/
def tableTruth (h : History W B T) (v : W) (e : B × B) : Prop :=
  h.ontic.Causes v e.1 e.2

/-- `r` and `f` are not coextensive on the worlds accessible from `a`. -/
def IndependentOf (c : Case W B T F) (a : W) (r f : F) : Prop :=
  ¬ ∀ v, c.history.ontic.frame.access a v → (c.holds v r ↔ c.holds v f)

/-- A true reason for each fact separating `a` from a rival, itself separating them.
This contrastive demand is a parameter, not a defended principle. -/
def ContrastiveClosure (c : Case W B T F) (a : W) : Prop :=
  ∀ b, Rival c.history a b → ∀ f, c.holds a f → ¬ c.holds b f →
    ∃ r, c.explains a r f ∧ c.holds a r ∧ ¬ c.holds b r

/-- If every conjunct of the total fact has a reason, so does the total fact. A
Hume-Edwards style bridge, stated as a testable condition; no author is cited for it. -/
def MemberLift (c : Case W B T F) (a : W) : Prop :=
  (∀ g, c.conjunct g (c.total a) → Explained c.arena a g) →
    Explained c.arena a (c.total a)

/-! ## Transporting causal-group records to a tagged copy -/

/-- A disjoint copy of a group record at tag `t`, with the same group indices. -/
def tagged {E G : Type} (t : Bool) (H : Groups E G) : Groups (Bool × E) G where
  contributors := fun g => {e | e.1 = t ∧ e.2 ∈ H.contributors g}
  enablers := fun g => {e | e.1 = t ∧ e.2 ∈ H.enablers g}
  effect := fun g => (t, H.effect g)
  admitted := H.admitted

/-- The tagged copy of a contribution or activity predicate. -/
def tagP {E : Type} (t : Bool) (P : E → Prop) (e : Bool × E) : Prop :=
  e.1 = t ∧ P e.2

/-- The tagged copy of an exercise, over the same scenarios. -/
def taggedExercise {R E G S : Type} (t : Bool) (m : Exercise R E G S) :
    Exercise (Bool × R) (Bool × E) G S where
  groups := tagged t m.groups
  bearer := fun e => (e.1, m.bearer e.2)
  occurs := fun s => tagP t (m.occurs s)
  allowed := m.allowed
  actual := m.actual
  exercised := m.exercised

/-! ## General theorems -/

/-- General implications. Coverage in `fork` is not exclusivity: two different
reasons may fall in the second and third disjuncts. -/
def Schema : Prop :=
  -- Coherence, joint sufficiency, Supply and local power survive tagged copying.
  (∀ (R E G S : Type) (t : Bool) (m : Exercise R E G S),
    (m.coherent → (taggedExercise t m).coherent) ∧
    (∀ g, m.jointlySufficient g → (taggedExercise t m).jointlySufficient g)) ∧
  (∀ (E G : Type) (t : Bool) (H : Groups E G) (I A : E → Prop),
    (∀ e, Supply H I e → Supply (tagged t H) (tagP t I) (t, e)) ∧
    (LocalPower H I A → LocalPower (tagged t H) (tagP t I) (tagP t A))) ∧
  -- Given `LocalRecord` at both worlds, same table iff same total.
  (∀ (W B T : Type) (h : History W B T) (a v : W), LocalRecord h a → LocalRecord h v →
    (SameTable h v a ↔ SameTotal h v a)) ∧
  -- So the named table selects, at `a`, whenever accessible worlds satisfy it.
  (∀ (W B T : Type) (h : History W B T) (a : W), LocalRecord h a →
    (∀ v, h.ontic.frame.access a v → LocalRecord h v) →
    ∃ p, EvidenceOnly (tableTruth h) (fun _ => True) p ∧ Selects h p a) ∧
  -- A fact tracking that table on accessible worlds is coextensive with the total.
  (∀ (W B T F : Type) (c : Case W B T F) (a : W) (r : F),
    LocalRecord c.history a →
    (∀ v, c.history.ontic.frame.access a v → LocalRecord c.history v) →
    (∀ v, c.history.ontic.frame.access a v → (c.holds v r ↔ SameTable c.history v a)) →
    ¬ IndependentOf c a r (c.total a)) ∧
  -- The indexical diagonal is trivial while the rigid total is contingent.
  (∀ (W B T F : Type) (c : Case W B T F) (a b : W), Rival c.history a b →
    (∀ w, c.holds w (c.total w)) ∧ Contingent c.arena a (c.total a)) ∧
  -- Fork at a rival, given factive reasons for the total.
  (∀ (W B T F : Type) (c : Case W B T F) (a b : W), Rival c.history a b →
    (∀ r, c.explains a r (c.total a) → c.holds a r) →
    ¬ Explained c.arena a (c.total a) ∨
    (∃ r, c.explains a r (c.total a) ∧ c.holds b r ∧ ¬ c.holds b (c.total a)) ∨
    (∃ r, c.explains a r (c.total a) ∧ ¬ c.holds b r ∧ Contingent c.arena a r)) ∧
  -- Inconsistent: rival; `r` true at `a` and all accessible worlds; `r` entails the total.
  (∀ (W B T F : Type) (c : Case W B T F) (a b : W) (r : F), Rival c.history a b →
    (∀ v, c.history.ontic.frame.access a v → c.holds v r) → c.holds a r →
    (∀ v, c.history.ontic.frame.access a v → c.holds v r → c.holds v (c.total a)) → False) ∧
  -- Inconsistent: rival; contrastive closure; well-founded reasons at `a`.
  (∀ (W B T F : Type) (c : Case W B T F) (a b : W), Rival c.history a b →
    ContrastiveClosure c a → WellFounded (c.explains a) → False)

/-! ## One signature for every causal form and every answer -/

/-- Worlds are (tag, bit). The tag fixes the population; the bit changes no history. -/
abbrev World := Bool × Bool
def actual : World := (false, true)
def duplicate : World := (false, false)
def rival : World := (true, true)

/-- The answers compared on each causal form. `ground` is one
structure for a necessary personal or impersonal ground: no predicate separates them. -/
inductive Policy | brute | internal | copy | ground | law deriving DecidableEq

inductive Fact
  | member (x : Bool × Nat)
  | total (t : Bool)
  | record (t : Bool)
  | ground
  | marker

abbrev Being := Option (Bool × Nat)

open TruthCore.Explanation.UltimateAdequacy (Kind groups intrinsic exercise)

/-- Edges are the tagged #735 edges of form `k`; under `ground`, a ground also has
an edge to each member of the world's population. -/
def causes (k : Kind) (p : Policy) (w : World) : Being → Being → Prop
  | some y, some x => y.1 = w.1 ∧ x.1 = w.1 ∧ (groups k).graph.edge y.2 x.2
  | none, some x => p = .ground ∧ x.1 = w.1
  | _, none => False

def present (p : Policy) (w : World) : Being → Prop
  | some x => x.1 = w.1
  | none => p = .ground

/-- Accessibility is universal when `o` is true and identity otherwise. -/
def history (o : Bool) (k : Kind) (p : Policy) : History World Being Nat where
  ontic := {
    frame := ⟨fun v w => o = true ∨ v = w⟩
    ExistsAt := present p
    Causes := causes k p }
  IsAt := fun w x _ => present p w x
  now := 0

def holdsAt (p : Policy) (w : World) : Fact → Prop
  | .member x => x.1 = w.1
  | .total t => t = w.1
  | .record t => t = w.1
  | .ground => p = .ground
  | .marker => p = .law ∧ w = actual

/-- Member-to-member reasons follow form `k` under every policy. Only the reasons for
aggregates, and the `ground` and `marker` reasons, vary. -/
def reasonFor (k : Kind) (p : Policy) (w : World) : Fact → Fact → Prop
  | .member y, .member x => y.1 = w.1 ∧ x.1 = w.1 ∧ (groups k).graph.edge y.2 x.2
  | .member y, .total t => p = .internal ∧ t = w.1 ∧ y = (t, 0)
  | .member y, .record t => p = .internal ∧ t = w.1 ∧ y = (t, 0)
  | .record s, .total t => p = .copy ∧ s = t ∧ t = w.1
  | .total s, .record t => p = .copy ∧ s = t ∧ t = w.1
  | .ground, .member x => p = .ground ∧ x.1 = w.1
  | .ground, .total t => p = .ground ∧ t = w.1
  | .ground, .record t => p = .ground ∧ t = w.1
  | .marker, .total t => p = .law ∧ w = actual ∧ t = false
  | _, _ => False

/-- Only member facts are recorded as conjuncts of a total fact. -/
def partOf : Fact → Fact → Prop
  | .member x, .total t => x.1 = t
  | _, _ => False

/-- The named edge table with names erased: which indices are linked somewhere. -/
def anonymous (k : Kind) (p : Policy) (w : World) (e : Nat × Nat) : Prop :=
  ∃ y x, causes k p w (some y) (some x) ∧ y.2 = e.1 ∧ x.2 = e.2

/-! ## Closed controls -/

/-- A causally idle existent differs while the table is the same. Deletes `Recorded`. -/
def idle : History Bool Bool Nat where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => x = w,
             Causes := fun _ _ _ => False }
  IsAt := fun w x _ => x = w
  now := 0

/-- Edges without existents at `true`. Deletes `Sound`. -/
def phantom : History Bool Unit Nat where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = false,
             Causes := fun _ _ _ => True }
  IsAt := fun w _ _ => w = false
  now := 0

/-- Same existents and table, re-dated presence. Deletes `Perpetual`. -/
def dated : History Bool Unit Nat where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => True }
  IsAt := fun w _ t => t = 0 ∨ w = false
  now := 0

/-- Presence and edges depend on a world only through its tag. -/
theorem same_of_tag (o : Bool) (k : Kind) (p : Policy) {v a : World} (h : v.1 = a.1) :
    SameTotal (history o k p) v a := by
  constructor
  · intro x _
    cases x with
    | none => exact Iff.rfl
    | some x => change x.1 = v.1 ↔ x.1 = a.1; rw [h]
  · intro y x
    cases y <;> cases x <;> simp only [history, causes, h]

theorem total_iff (o : Bool) (k : Kind) (p : Policy) (a v : World) :
    holdsAt p v (.total a.1) ↔ SameTotal (history o k p) v a := by
  constructor
  · intro h
    exact same_of_tag o k p h.symm
  · intro h
    have := (h.1 (some (a.1, 0)) 0).2 rfl
    exact this

/-- Each policy and causal form is one `Case`, with the same total fact. -/
def case (o : Bool) (k : Kind) (p : Policy) : Case World Being Nat Fact where
  history := history o k p
  holds := holdsAt p
  exist := fun x => match x with
    | some x => .member x
    | none => .ground
  explains := reasonFor k p
  conjunct := partOf
  total := fun w => .total w.1
  total_holds := total_iff o k p

/-- The same tagged member records under each answer; `ground` adds one being and
its edges. Each answer is witnessed at `actual`. Isolation removes the rival, and
three models each violate one clause of `LocalRecord`. These are analyst models: none is a defended ontology, none
establishes real possibility, and `ground` does not distinguish personal choice. -/
def Controls : Prop :=
  -- Background on every causal form.
  (∀ o k p w, LocalRecord (history o k p) w) ∧
  (∀ k p, Rival (history true k p) actual rival) ∧
  (∀ k t, (taggedExercise t (exercise k)).coherent ∧
    (∀ g, (taggedExercise t (exercise k)).jointlySufficient g) ∧
    LocalPower (tagged t (groups k)) (tagP t (intrinsic k))
      (tagP t ((exercise k).occurs (exercise k).actual))) ∧
  (∀ o k p (w : World) y x, (history o k p).ontic.Causes w (some y) (some x) ↔
    (tagged w.1 (groups k)).graph.edge y x) ∧
  (∀ t e, Supply (tagged t (groups .single)) (tagP t (intrinsic .single)) (t, e)) ∧
  (∀ t e, Supply (tagged t (groups .plural)) (tagP t (intrinsic .plural)) (t, e)) ∧
  -- Named records select at either designation; the same records with names erased do not.
  (∀ k p a, ∃ q, EvidenceOnly (tableTruth (history true k p)) (fun _ => True) q ∧
    Selects (history true k p) q a) ∧
  (∀ k p (a : World), ¬ ∃ q, EvidenceOnly (anonymous k p) (fun _ => True) q ∧
    Selects (history true k p) q a) ∧
  -- Brute: no reason for the total; on the chain every existent still has one.
  (∀ k, ¬ Explained (case true k .brute).arena actual (.total false) ∧
    ¬ ContingentPSR (case true k .brute).arena actual ∧
    ¬ ContrastiveClosure (case true k .brute) actual) ∧
  (∀ w, ExistencePSR (case true .chain .brute).arena w) ∧
  ¬ MemberLift (case true .chain .brute) actual ∧
  -- Internal: a member separates the total from the rival, coextensively in this fixture.
  (∀ k, (case true k .internal).explains actual (.member (false, 0)) (.total false) ∧
    Contingent (case true k .internal).arena actual (.member (false, 0)) ∧
    ¬ holdsAt .internal rival (.member (false, 0)) ∧
    ¬ IndependentOf (case true k .internal) actual (.member (false, 0)) (.total false)) ∧
  (∀ k, ContrastiveClosure (case true k .internal) actual ↔ k = .chain) ∧
  WellFounded ((case true .single .internal).explains actual) ∧
  WellFounded ((case true .plural .internal).explains actual) ∧
  ¬ WellFounded ((case true .chain .internal).explains actual) ∧
  (∀ w, ContingentPSR (case true .chain .internal).arena w) ∧
  -- Copy: the aggregate record is a reason for the total, not independently of it.
  (∀ k, (case true k .copy).explains actual (.record false) (.total false) ∧
    (∀ v, holdsAt .copy v (.record false) ↔ SameTable (history true k .copy) v actual) ∧
    ¬ IndependentOf (case true k .copy) actual (.record false) (.total false)) ∧
  MemberLift (case true .chain .copy) actual ∧
  ContrastiveClosure (case true .chain .copy) actual ∧
  (∀ w, ContingentPSR (case true .chain .copy).arena w) ∧
  -- Ground: every contingent truth has a reason at every world, and the reason
  -- for the total holds at the rival, where the total fails.
  (∀ k, (∀ w, ContingentPSR (case true k .ground).arena w) ∧
    Factive (case true k .ground).arena ∧
    ¬ Necessitating (case true k .ground).arena ∧
    (case true k .ground).explains actual .ground (.total false) ∧
    (∀ w, holdsAt .ground w .ground) ∧
    ¬ holdsAt .ground rival (.total false) ∧
    IndependentOf (case true k .ground) actual .ground (.total false) ∧
    ¬ ContrastiveClosure (case true k .ground) actual) ∧
  -- Law: a contingent, independent, entailing reason that itself lacks a reason.
  (∀ k, (case true k .law).explains actual .marker (.total false) ∧
    Contingent (case true k .law).arena actual .marker ∧
    (∀ v, holdsAt .law v .marker → holdsAt .law v (.total false)) ∧
    IndependentOf (case true k .law) actual .marker (.total false) ∧
    ¬ Explained (case true k .law).arena actual .marker ∧
    ¬ ContingentPSR (case true k .law).arena actual ∧
    ¬ ContrastiveClosure (case true k .law) actual) ∧
  -- Isolation: no rival, and the other members of both cores hold.
  (∀ k p b, ¬ Rival (history false k p) actual b) ∧
  (∀ k p, ¬ Contingent (case false k p).arena actual (.total false)) ∧
  (∀ k, (case false k .ground).explains actual .ground (.total false) ∧
    ∀ v, (history false k .ground).ontic.frame.access actual v →
      holdsAt .ground v .ground ∧ holdsAt .ground v (.total false)) ∧
  ContrastiveClosure (case false .single .internal) actual ∧
  WellFounded ((case false .single .internal).explains actual) ∧
  -- One clause of `LocalRecord` fails at `true`, the other two hold there, and
  -- the tables agree while the totals differ.
  (SameTable idle true false ∧ ¬ SameTotal idle true false ∧ ¬ Recorded idle true ∧
    Sound idle true ∧ Perpetual idle true) ∧
  (SameTable phantom true false ∧ ¬ SameTotal phantom true false ∧ ¬ Sound phantom true ∧
    Recorded phantom true ∧ Perpetual phantom true) ∧
  (SameTable dated true false ∧ ¬ SameTotal dated true false ∧ ¬ Perpetual dated true ∧
    Sound dated true ∧ Recorded dated true)

end TruthCore.Explanation.ActualWorldGap
