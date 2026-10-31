import Mathlib.Logic.Relation
import Mathlib.Order.Basic
import TruthCore.Explanation.ExplanatoryAdequacy

/-!
# Selecting one outcome over another with a reason true at both (#742)

#750 left this open: how is a reason true at a world and at its rival relevant to which
outcome obtains? This module adds that relevance as one explicit parameter, `favours`, and
tests what follows under named conditions on it. `favours` is an interpreted parameter, as
`explains` is in #755. No clause below says that adequate selection is necessitation, and
nothing is asserted of reality. See `docs/notes/explanatory-symmetry-742.md` for the
interpretation, the examples and the rival accounts.
-/
namespace TruthCore.Explanation.ExplanatorySymmetry

open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.HistorySelection

variable {W B F : Type}

/-- An arena with a favouring parameter. `favours w r f g` is read: at `w`, the fact `r`
counts in favour of `f` over `g`. It is not assumed necessitating, probabilistic, causal,
asymmetric or stable across worlds. -/
structure Frame (W B F : Type) where
  arena : Arena W B F
  favours : W → F → F → F → Prop

/-- `v` is `a` or accessible from `a`. -/
def Worlds (A : Arena W B F) (a v : W) : Prop := v = a ∨ Access A a v

/-- Which reasons favour what is settled by which basic facts are true: worlds agreeing on
the truth of all of `base` agree on the favouring by each member of `base`. A reason's
favouring may vary with the truth of other base facts, and it may not vary otherwise. -/
def BaseFixed (X : Frame W B F) (base : F → Prop) : Prop :=
  ∀ v w r f g, SameEvidence X.arena.holds base v w → base r →
    (X.favours v r f g ↔ X.favours w r f g)

/-- No member of `base` favours one outcome over a second and the second over the first. -/
def Asymmetric (X : Frame W B F) (base : F → Prop) : Prop :=
  ∀ w r f g, base r → X.favours w r f g → ¬ X.favours w r g f

/-- A true base reason is admitted for the true `f`, the rival `g` is false, and the reason
favours `f` over `g`. Other base reasons may favour `g` over `f`. -/
def ProTanto (X : Frame W B F) (base : F → Prop) (w : W) (r f g : F) : Prop :=
  base r ∧ X.arena.holds w r ∧ X.arena.holds w f ∧ ¬ X.arena.holds w g ∧
    X.arena.explains w r f ∧ X.favours w r f g

/-- Some base reason favours `f` over `g` pro tanto, and at `w` no true member of `base`
favours `g` over `f`. -/
def NetSelects (X : Frame W B F) (base : F → Prop) (w : W) (f g : F) : Prop :=
  (∃ r, ProTanto X base w r f g) ∧ ∀ s, base s → X.arena.holds w s → ¬ X.favours w s g f

/-- At `w`, each true member of the outcome field is net-selected over each false member. -/
def SelectedAt (X : Frame W B F) (base O : F → Prop) (w : W) : Prop :=
  ∀ f g, O f → O g → X.arena.holds w f → ¬ X.arena.holds w g → NetSelects X base w f g

/-- At `w`, each true member of the field has a pro tanto reason over each false member. -/
def ProTantoAt (X : Frame W B F) (base O : F → Prop) (w : W) : Prop :=
  ∀ f g, O f → O g → X.arena.holds w f → ¬ X.arena.holds w g → ∃ r, ProTanto X base w r f g

/-- Some member of the outcome field is true at `v`. -/
def ExhaustiveAt (A : Arena W B F) (O : F → Prop) (v : W) : Prop :=
  ∃ g, O g ∧ A.holds v g

/-- At most one member of the outcome field is true at `v`. -/
def ExclusiveAt (A : Arena W B F) (O : F → Prop) (v : W) : Prop :=
  ∀ f g, O f → O g → A.holds v f → A.holds v g → f = g

/-- Every member of `base` is true at `a` and at every world accessible from `a`. -/
def NecessaryBase (A : Arena W B F) (base : F → Prop) (a : W) : Prop :=
  ∀ r v, base r → Worlds A a v → A.holds v r

/-! ## Favouring structures -/

/-- Favouring read from one ranking of outcomes, whichever reason is considered. The ranking
is any Mathlib preorder, as a good order or a single weight of outcomes would be. -/
def scalar {V : Type} [Preorder V] (A : Arena W B F) (q : F → V) : Frame W B F :=
  ⟨A, fun _ _ f g => q g < q f⟩

/-- Favouring read from a ranking of outcomes per reason, so reasons may rank them oppositely. -/
def perReason {V : Type} [Preorder V] (A : Arena W B F) (q : F → F → V) : Frame W B F :=
  ⟨A, fun _ r f g => q r g < q r f⟩

/-- Favouring settled by the outcome: a reason favours what is true over what is false. -/
def settled (A : Arena W B F) : Frame W B F :=
  ⟨A, fun w _ f g => A.holds w f ∧ ¬ A.holds w g⟩

/-- A favouring whose instances all report the outcome pair at that world. -/
def FactiveFavour (X : Frame W B F) : Prop :=
  ∀ w r f g, X.favours w r f g → X.arena.holds w f ∧ ¬ X.arena.holds w g

/-- The arena of `tokenExpand`, with the token favouring anything over anything. Nothing in
the expansion makes the token relevant to anything. -/
def tokenFrame (A : Arena W B F) : Frame W B (Option F) :=
  ⟨tokenExpand A, fun _ r _ _ => r = none⟩

/-- The token is the only base member of `tokenFrame`. -/
def tokenBase : Option F → Prop := fun r => r = none

/-! ## Modal difference-making -/

/-- Wherever an accessible world lacks `r`, it lacks `f`. This is the modal reading of "had
the reason been absent, the outcome would have been absent". -/
def Enables (A : Arena W B F) (a : W) (r f : F) : Prop :=
  ∀ v, Access A a v → ¬ A.holds v r → ¬ A.holds v f

/-- `r` enables `f` and some accessible world lacks `r`, so the test has a case to pass. -/
def EnablesNonvacuously (A : Arena W B F) (a : W) (r f : F) : Prop :=
  Enables A a r f ∧ ∃ v, Access A a v ∧ ¬ A.holds v r

/-- Every reason for a contingent member of the account nonvacuously enables it. -/
def AllReasonsEnable (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ r f, S f → Contingent A a f → A.explains a r f → EnablesNonvacuously A a r f

/-! ## Marks a personal choice is said to have -/

/-- Structural marks offered for a choice among outcomes, tested as a single bundle.

* `twoWay`: at each of `a` and its accessible worlds, each true field member has a pro tanto
  reason over each false one.
* `plural`: two distinct base reasons rank some outcome pair oppositely.
* `interposed`: each true field member at such a world has an act `c`, reached by a true base
  reason and a reason for the member, and true at a world accessible from `a` only with it.
* `open_`: each contingent field member at `a` has an admitted base reason true at a world
  accessible from `a` that lacks the member. -/
structure Marks (X : Frame W B F) (base O : F → Prop) (a : W) : Prop where
  twoWay : ∀ w, Worlds X.arena a w → ProTantoAt X base O w
  plural : ∃ r s f g, base r ∧ base s ∧ r ≠ s ∧ X.favours a r f g ∧ X.favours a s g f
  interposed : ∀ w f, Worlds X.arena a w → O f → X.arena.holds w f →
    ∃ r c, base r ∧ X.arena.holds w r ∧ X.arena.explains w r c ∧ X.arena.explains w c f ∧
      ∀ v, Access X.arena a v → X.arena.holds v c → X.arena.holds v f
  open_ : ∀ f, O f → Contingent X.arena a f →
    ∃ r v, base r ∧ X.arena.explains a r f ∧ Access X.arena a v ∧
      X.arena.holds v r ∧ ¬ X.arena.holds v f

/-- A base member is the existence fact of a bearer with the supplied flag. The flag is an
uninterpreted parameter, so this standard names its expected satisfier. It is the circular
control, in the role of `BeingStop` in #750. -/
def PersonalStop (X : Frame W B F) (base : F → Prop) (personal : B → Prop) : Prop :=
  ∃ x, personal x ∧ base (X.arena.exist x)

/-! ## Models on the signature of #750 -/

/-- The field of rival outcomes in `ground`, `plural`, `law` and `necessitarian`. -/
inductive Rival : Fact → Prop
  | target : Rival .target
  | other : Rival .other

/-- The one necessary source of #750. -/
def oneSource : Fact → Prop := fun r => r = .source true

/-- Both necessary sources of `plural` in #750. -/
def twoSources : Fact → Prop := fun r => r = .source true ∨ r = .source false

/-- The target ranks above the rival outcome, whichever reason is read. -/
def targetFirst : Fact → Nat
  | .target => 1
  | _ => 0

/-- `ground` with one ranking of outcomes. The reason holds at both worlds of the rival pair. -/
def oneWay : Frame Nat (Option Bool) Fact := scalar ground targetFirst

/-- Source `true` ranks the target first and source `false` ranks the rival outcome first. -/
def tendency : Fact → Fact → Nat
  | .source true, .target => 1
  | .source false, .other => 1
  | _, _ => 0

/-- Truth with both necessary sources of `plural`, and an act `member 0` for the target and
an act `member 1` for the rival outcome, each true exactly with its outcome. -/
def actingHolds : Nat → Fact → Prop
  | w, .target => w = 0
  | w, .other => w ≠ 0
  | _, .source _ => True
  | w, .member n => (n = 0 ∧ w = 0) ∨ (n = 1 ∧ w ≠ 0)
  | _, .whole => False

/-- Each source is a reason for the act and outcome it ranks first; each act for its outcome. -/
inductive ActingReason : Nat → Fact → Fact → Prop
  | sourceTarget : ActingReason 0 (.source true) .target
  | sourceAct : ActingReason 0 (.source true) (.member 0)
  | actTarget : ActingReason 0 (.member 0) .target
  | sourceOther (w : Nat) : w ≠ 0 → ActingReason w (.source false) .other
  | sourceRival (w : Nat) : w ≠ 0 → ActingReason w (.source false) (.member 1)
  | actOther (w : Nat) : w ≠ 0 → ActingReason w (.member 1) .other

/-- Necessary reasons with opposite rankings, and acts between them and the outcomes. The
frame has no flag for a person: `PersonalStop` takes the flag as a separate argument. -/
def acting : Frame Nat (Option Bool) Fact :=
  perReason (rival actingHolds ActingReason) tendency

/-- Truth with contingent reasons. Member `0` holds only at `0`, member `1` at each world
except `0` and `2`, and member `2` only at `2`. The target holds at `0` and `2`. -/
def varyingHolds : Nat → Fact → Prop
  | w, .target => w = 0 ∨ w = 2
  | w, .other => w ≠ 0 ∧ w ≠ 2
  | _, .source _ => False
  | w, .member 0 => w = 0
  | w, .member 1 => w ≠ 0 ∧ w ≠ 2
  | w, .member 2 => w = 2
  | _, .member _ => False
  | _, .whole => False

/-- Each world's true member is the reason for its true outcome. -/
inductive VaryingReason : Nat → Fact → Fact → Prop
  | zero : VaryingReason 0 (.member 0) .target
  | two : VaryingReason 2 (.member 2) .target
  | one (w : Nat) : w ≠ 0 → w ≠ 2 → VaryingReason w (.member 1) .other

/-- The base members of `varying`. -/
def varyingBase : Fact → Prop :=
  fun r => r = .member 0 ∨ r = .member 1 ∨ r = .member 2

/-- Members `0` and `2` rank the target first, and member `1` the rival outcome. -/
def varyingTendency : Fact → Fact → Nat
  | .member 0, .target => 1
  | .member 2, .target => 1
  | .member 1, .other => 1
  | _, _ => 0

/-- Reasons that differ between rival histories, whose favouring does not vary. -/
def varying : Frame Nat (Option Bool) Fact :=
  perReason (rival varyingHolds VaryingReason) varyingTendency

/-- Truth with the rival outcome everywhere and the target only at `0`, so both are true
there. Source `true` is true everywhere. -/
def overlapHolds : Nat → Fact → Prop
  | w, .target => w = 0
  | _, .other => True
  | _, .source i => i = true
  | _, .member _ => False
  | _, .whole => False

/-- Source `true` is a reason for the rival outcome where the target is false. -/
inductive OverlapReason : Nat → Fact → Fact → Prop
  | step (w : Nat) : w ≠ 0 → OverlapReason w (.source true) .other

/-- The rival outcome ranks above the target. -/
def otherFirst : Fact → Nat
  | .other => 1
  | _ => 0

/-- Two outcomes that do not exclude each other at `0`. -/
def overlap : Frame Nat (Option Bool) Fact :=
  scalar (rival overlapHolds OverlapReason) otherFirst

/-- An arena with no favouring at all. -/
def favourless (A : Arena W B F) : Frame W B F := ⟨A, fun _ _ _ _ => False⟩

/-! ## Certificates -/

/-- The incompatible core and a deletion witness for each member.

First conjunct: no frame has two worlds `a` and `v` that agree on the whole base, with
base-fixed favouring, net selection at both, a field member true at `v`, at most one true
at `a`, and a field member `f` true at `a` and false at `v`. No clause says a reason
necessitates. Second conjunct: if the base holds at `a` and its accessible worlds, favouring
is base-fixed, and those worlds all have net selection and exactly one true field member, then
no field member is contingent at `a`.

Remaining conjuncts each keep the other members of the first bundle and refute the deleted
one, which certifies inclusion-minimality of that bundle (not minimum cardinality, and nothing
about the second). The core forces rejection of at least one member and chooses none. -/
def Core : Prop :=
  (∀ (W B F : Type) (X : Frame W B F) (base O : F → Prop) (a v : W) (f : F),
    SameEvidence X.arena.holds base a v → BaseFixed X base →
    SelectedAt X base O a → SelectedAt X base O v →
    ExhaustiveAt X.arena O v → ExclusiveAt X.arena O a →
    O f → X.arena.holds a f → ¬ X.arena.holds v f → False) ∧
  (∀ (W B F : Type) (X : Frame W B F) (base O : F → Prop) (a : W) (f : F),
    NecessaryBase X.arena base a → BaseFixed X base →
    (∀ w, Worlds X.arena a w → SelectedAt X base O w) →
    (∀ w, Worlds X.arena a w → ExhaustiveAt X.arena O w) →
    (∀ w, Worlds X.arena a w → ExclusiveAt X.arena O w) →
    O f → ¬ Contingent X.arena a f) ∧
  -- delete agreement on the base: reasons that vary with the outcome
  (¬ SameEvidence varying.arena.holds varyingBase 0 1 ∧ BaseFixed varying varyingBase ∧
    SelectedAt varying varyingBase Rival 0 ∧ SelectedAt varying varyingBase Rival 1 ∧
    ExhaustiveAt varying.arena Rival 1 ∧ ExclusiveAt varying.arena Rival 0 ∧
    Rival .target ∧ varying.arena.holds 0 .target ∧ ¬ varying.arena.holds 1 .target ∧
    Contingent varying.arena 0 (.member 0) ∧ ∀ S, ¬ ReasonClosed varying.arena 0 S .target) ∧
  -- delete base-fixed favouring: favouring settled by the outcome
  (SameEvidence (settled ground).arena.holds oneSource 0 1 ∧ ¬ BaseFixed (settled ground) oneSource ∧
    SelectedAt (settled ground) oneSource Rival 0 ∧ SelectedAt (settled ground) oneSource Rival 1 ∧
    ExhaustiveAt ground Rival 1 ∧ ExclusiveAt ground Rival 0 ∧
    Rival .target ∧ ground.holds 0 .target ∧ ¬ ground.holds 1 .target) ∧
  -- delete selection at the rival world: one ranking, with the favoured outcome true at `0`
  (SameEvidence ground.holds oneSource 0 1 ∧ BaseFixed oneWay oneSource ∧
    SelectedAt oneWay oneSource Rival 0 ∧ ¬ SelectedAt oneWay oneSource Rival 1 ∧
    ExhaustiveAt ground Rival 1 ∧ ExclusiveAt ground Rival 0 ∧
    Rival .target ∧ ground.holds 0 .target ∧ ¬ ground.holds 1 .target) ∧
  -- delete selection at the designated world: the same ranking, with `1` designated
  (SameEvidence ground.holds oneSource 1 0 ∧ BaseFixed oneWay oneSource ∧
    ¬ SelectedAt oneWay oneSource Rival 1 ∧ SelectedAt oneWay oneSource Rival 0 ∧
    ExhaustiveAt ground Rival 0 ∧ ExclusiveAt ground Rival 1 ∧
    Rival .other ∧ ground.holds 1 .other ∧ ¬ ground.holds 0 .other) ∧
  -- delete a true field member at the rival: #755's necessary ground, with no rival outcome fact
  (SameEvidence (PSRStrength.ground true).holds (· = GroundFact.ground) false true ∧
    BaseFixed (favourless (PSRStrength.ground true)) (· = GroundFact.ground) ∧
    SelectedAt (favourless (PSRStrength.ground true)) (· = GroundFact.ground)
      (· = GroundFact.choice) false ∧
    SelectedAt (favourless (PSRStrength.ground true)) (· = GroundFact.ground)
      (· = GroundFact.choice) true ∧
    ¬ ExhaustiveAt (PSRStrength.ground true) (· = GroundFact.choice) true ∧
    ExclusiveAt (PSRStrength.ground true) (· = GroundFact.choice) false ∧
    (PSRStrength.ground true).holds false GroundFact.choice ∧
    ¬ (PSRStrength.ground true).holds true GroundFact.choice) ∧
  -- delete exclusivity: the rival outcome true together with the target at `0`
  (SameEvidence overlap.arena.holds oneSource 0 1 ∧ BaseFixed overlap oneSource ∧
    SelectedAt overlap oneSource Rival 0 ∧ SelectedAt overlap oneSource Rival 1 ∧
    ExhaustiveAt overlap.arena Rival 1 ∧ ¬ ExclusiveAt overlap.arena Rival 0 ∧
    Rival .target ∧ overlap.arena.holds 0 .target ∧ ¬ overlap.arena.holds 1 .target) ∧
  -- delete field membership: the contingent target is outside the field
  (SameEvidence ground.holds oneSource 0 1 ∧ BaseFixed (favourless ground) oneSource ∧
    SelectedAt (favourless ground) oneSource oneSource 0 ∧
    SelectedAt (favourless ground) oneSource oneSource 1 ∧
    ExhaustiveAt ground oneSource 1 ∧ ExclusiveAt ground oneSource 0 ∧
    ¬ oneSource .target ∧ ground.holds 0 .target ∧ ¬ ground.holds 1 .target) ∧
  -- delete truth at the designated world: the rival outcome is false throughout #750's no-rival model
  (SameEvidence necessitarian.holds oneSource 0 1 ∧
    BaseFixed (scalar necessitarian targetFirst) oneSource ∧
    SelectedAt (scalar necessitarian targetFirst) oneSource Rival 0 ∧
    SelectedAt (scalar necessitarian targetFirst) oneSource Rival 1 ∧
    ExhaustiveAt necessitarian Rival 1 ∧ ExclusiveAt necessitarian Rival 0 ∧
    Rival .other ∧ ¬ necessitarian.holds 0 .other ∧ ¬ necessitarian.holds 1 .other) ∧
  -- delete falsity at the rival: #750's no-rival model, where the target holds at both
  (SameEvidence necessitarian.holds oneSource 0 1 ∧
    BaseFixed (scalar necessitarian targetFirst) oneSource ∧
    SelectedAt (scalar necessitarian targetFirst) oneSource Rival 0 ∧
    SelectedAt (scalar necessitarian targetFirst) oneSource Rival 1 ∧
    ExhaustiveAt necessitarian Rival 1 ∧ ExclusiveAt necessitarian Rival 0 ∧
    Rival .target ∧ necessitarian.holds 0 .target ∧ necessitarian.holds 1 .target)

/-- What each candidate reading of selection delivers. Each clause is a conditional
consequence or a verdict on a named analyst-built model.

* One reason: with base-fixed asymmetric favouring, worlds agreeing on the base do not have
  one base reason favouring `f` over `g` pro tanto at one and `g` over `f` at the other. On
  `ground`, favouring everything over everything keeps both pro tanto instances and is not
  asymmetric.
* Plural reasons: with base-fixed favouring, opposite pro tanto reasons at two worlds agreeing
  on the base refute net selection at both.
* Marks: `acting` has all `Marks` at world `0` with base-fixed favouring and has no net
  selection at `0` or at `1`. The flag of `PersonalStop` holds there exactly when it is
  supplied as true, and `Marks` takes no flag.
* Interposed acts: along any reason path from a fact true at `v` to a fact false at `v`, not
  every reason link of the arena preserves truth at `v`. If `c` true at `v` would give `f`, and
  `r` is true and `f` false at `v`, then `c` is false at `v` while `r` is true there.
* Scalar and per-reason rankings: no scalar frame has opposite pro tanto reasons at any two
  worlds. `acting` is per-reason and is not scalar on `Rival` for any `Nat` ranking. On `ground`
  with a constant ranking no pro tanto instance exists. `oneWay` net-selects the target at `0`,
  with its reason true and the target false at `1`, and does not net-select the rival at `1`.
* Settled favouring: if a frame's favouring is factive and `w` has net selection, then for field
  members some base reason favours `f` over `g` at `w` exactly when `f` is true and `g` false. `settled ground` is factive and has net selection at every world.
* Difference-making: a fact true at every accessible world enables every fact, and the token of
  `tokenExpand` enables every fact. Nonvacuous enabling by a true reason makes the reason contingent.
  With reason closure, foundedness and a contingent explanandum, reasons that all nonvacuously
  enable are inconsistent by the #750 core. `brute` has a nonvacuously enabling reason that does
  not necessitate.
* Tokens and beings: `tokenFrame` gives a pro tanto instance over each false fact for each
  contingent fact of any arena. Under one favouring, `ground` and `law` have one net-selection
  verdict at each world. -/
def Comparison : Prop :=
  -- one reason across two histories
  (∀ (W B F : Type) (X : Frame W B F) (base : F → Prop) (v w : W) (r f g : F),
    BaseFixed X base → Asymmetric X base → SameEvidence X.arena.holds base v w →
    ProTanto X base v r f g → ProTanto X base w r g f → False) ∧
  (BaseFixed (⟨ground, fun _ _ _ _ => True⟩ : Frame _ _ _) oneSource ∧
    ¬ Asymmetric (⟨ground, fun _ _ _ _ => True⟩ : Frame _ _ _) oneSource ∧
    ProTanto (⟨ground, fun _ _ _ _ => True⟩ : Frame _ _ _) oneSource 0 (.source true) .target .other ∧
    ProTanto (⟨ground, fun _ _ _ _ => True⟩ : Frame _ _ _) oneSource 1 (.source true) .other .target) ∧
  -- plural reasons
  (∀ (W B F : Type) (X : Frame W B F) (base : F → Prop) (v w : W) (r s f g : F),
    BaseFixed X base → SameEvidence X.arena.holds base v w →
    ProTanto X base v r f g → ProTanto X base w s g f →
    ¬ NetSelects X base v f g ∧ ¬ NetSelects X base w g f) ∧
  -- the marks of a choice, and the flag
  (Marks acting twoSources Rival 0 ∧ BaseFixed acting twoSources ∧
    NecessaryBase acting.arena twoSources 0 ∧ Contingent acting.arena 0 .target ∧
    ¬ NetSelects acting twoSources 0 .target .other ∧
    ¬ NetSelects acting twoSources 1 .other .target ∧
    ∀ p : Prop, PersonalStop acting twoSources (fun _ => p) ↔ p) ∧
  -- interposed acts
  (∀ (W B F : Type) (A : Arena W B F) (a v : W) (r f : F),
    Relation.ReflTransGen (A.explains a) r f → A.holds v r → ¬ A.holds v f →
    ¬ ∀ x y, A.explains a x y → A.holds v x → A.holds v y) ∧
  (∀ (W B F : Type) (A : Arena W B F) (v : W) (r c f : F),
    (A.holds v c → A.holds v f) → A.holds v r → ¬ A.holds v f →
    A.holds v r ∧ ¬ A.holds v c) ∧
  -- scalar and per-reason rankings
  (∀ (W B F V : Type) [Preorder V] (A : Arena W B F) (q : F → V) (base : F → Prop)
      (v w : W) (r s f g : F),
    ProTanto (scalar A q) base v r f g → ProTanto (scalar A q) base w s g f → False) ∧
  (¬ ∃ q : Fact → Nat, ∀ w r f g, twoSources r → Rival f → Rival g →
    (acting.favours w r f g ↔ q g < q f)) ∧
  (∀ (v : Nat) (r f g : Fact), ¬ ProTanto (scalar ground (fun _ => (0 : Nat))) oneSource v r f g) ∧
  (NetSelects oneWay oneSource 0 .target .other ∧ ground.holds 1 (.source true) ∧
    ¬ ground.holds 1 .target ∧ ¬ NetSelects oneWay oneSource 1 .other .target) ∧
  -- settled favouring
  (∀ (W B F : Type) (X : Frame W B F) (base O : F → Prop) (w : W) (f g : F),
    FactiveFavour X → SelectedAt X base O w → O f → O g →
    ((∃ r, base r ∧ X.favours w r f g) ↔ (X.arena.holds w f ∧ ¬ X.arena.holds w g))) ∧
  (FactiveFavour (settled ground) ∧ ∀ w, SelectedAt (settled ground) oneSource Rival w) ∧
  -- difference-making
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (r f : F),
    (∀ v, Access A a v → A.holds v r) → Enables A a r f) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (r f : F),
    A.holds a r → EnablesNonvacuously A a r f → Contingent A a r) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (f : Option F),
    Enables (tokenExpand A) a none f) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ReasonClosed A a S x → Contingent A a x → Founded A a S → AllReasonsEnable A a S → False) ∧
  (EnablesNonvacuously brute 0 (.source true) .target ∧
    ¬ ∀ v, Access brute 0 v → brute.holds v (.source true) → brute.holds v .target) ∧
  -- tokens and beings
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (f g : F),
    Contingent A w f → ¬ A.holds w g →
    ProTanto (tokenFrame A) tokenBase w none (some f) (some g)) ∧
  (∀ (φ : Nat → Fact → Fact → Fact → Prop) (base O : Fact → Prop) (w : Nat),
    SelectedAt ⟨ground, φ⟩ base O w ↔ SelectedAt ⟨law, φ⟩ base O w)

end TruthCore.Explanation.ExplanatorySymmetry
