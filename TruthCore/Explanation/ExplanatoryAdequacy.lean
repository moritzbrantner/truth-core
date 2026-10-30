import TruthCore.Explanation.PSRStrength
import TruthCore.Explanation.UltimateAdequacy

/-!
# Candidate standards of ultimate explanatory adequacy (#750)

Each standard below is a candidate under test, stated over the #755 `Arena`. None
is called "adequate" and none is asserted of reality. `explains` stays the
interpreted parameter of #755: the theorems say what follows when an analyst-built
interpretation admits a reason, not that the reason genuinely explains. See
`docs/notes/explanatory-adequacy-750.md` for the interpretation, sources and rivals.
-/
namespace TruthCore.Explanation.ExplanatoryAdequacy

open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference

variable {W B F : Type}

/-! ## Candidate standards -/

/-- `S` is reason-closed for `x` at `a`. `S` contains `x`, its members are true,
every reason admitted for a member is a member, every contingent member has a
reason, and no admitted reason for a contingent member is modally coextensive with
it. The clause `covered` refuses a contingent member with no reason by stipulation;
this is not an argument against such a stopping point. -/
structure ReasonClosed (A : Arena W B F) (a : W) (S : F → Prop) (x : F) : Prop where
  explanandum : S x
  truthful : ∀ f, S f → A.holds a f
  closed : ∀ r f, S f → A.explains a r f → S r
  covered : ∀ f, S f → Contingent A a f → ∃ r, A.explains a r f
  nonCopy : ∀ r f, S f → A.explains a r f → Contingent A a f →
    ¬ ∀ v, Access A a v → (A.holds v r ↔ A.holds v f)

/-- Each accessible world lacking a contingent member is excluded by some reason
for that member, which fails there. The reason may vary with the rival world. -/
def ContrastRelevant (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ f, S f → Contingent A a f → ∀ v, Access A a v → ¬ A.holds v f →
    ∃ r, S r ∧ A.explains a r f ∧ ¬ A.holds v r

/-- One reason for each contingent member excludes all of its rival worlds. -/
def UniformContrast (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ f, S f → Contingent A a f →
    ∃ r, S r ∧ A.explains a r f ∧ ∀ v, Access A a v → ¬ A.holds v f → ¬ A.holds v r

/-- For each rival world of a contingent member, some reason for the member also
is admitted at that world as a reason for a fact true there and false at `a`. -/
def TwoWay (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ f, S f → Contingent A a f → ∀ v, Access A a v → ¬ A.holds v f →
    ∃ r g, S r ∧ A.explains a r f ∧ A.holds v g ∧ ¬ A.holds a g ∧ A.explains v r g

/-- Every member that is not contingent is the existence fact of a necessary
being. This standard names the expected satisfier: it is the circular control. -/
def BeingStop (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ f, S f → ¬ Contingent A a f → ∃ x, f = A.exist x ∧ NecessaryAt A.ontic a x

/-- Every reason for a contingent member is contingent. -/
def AllReasonsVary (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ r f, S f → Contingent A a f → A.explains a r f → Contingent A a r

/-- Each reason for a contingent member modally suffices for it at `a`. -/
def AllReasonsNecessitate (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  ∀ r f, S f → Contingent A a f → A.explains a r f →
    ∀ v, Access A a v → A.holds v r → A.holds v f

/-- The reason relation among contingent members of `S`. -/
def ContingentReason (A : Arena W B F) (a : W) (S : F → Prop) (r f : F) : Prop :=
  S r ∧ S f ∧ A.explains a r f ∧ Contingent A a r ∧ Contingent A a f

/-- The contingent reason relation has no infinite descent and no cycle. -/
def Founded (A : Arena W B F) (a : W) (S : F → Prop) : Prop :=
  WellFounded (ContingentReason A a S)

/-- The arena with its beings removed. -/
def bare (A : Arena W B F) : Arena W Empty F :=
  basic (Access A) A.holds A.explains A.conjunct

/-! ## Token expansion -/

/-- The expansion's only reasons: the new token, for each contingent old truth. -/
inductive TokenReason (A : Arena W B F) : W → Option F → Option F → Prop
  | mk {w : W} {f : F} : Contingent A w f → TokenReason A w none (some f)

/-- Adds one fact `none`, true at every world, and replaces all reasons by that
token. Worlds, beings and the truth of old facts are unchanged. Nothing in the
expansion makes the token relevant to anything. -/
def tokenExpand (A : Arena W B F) : Arena W B (Option F) where
  ontic := A.ontic
  holds := fun w f => match f with
    | none => True
    | some f => A.holds w f
  exist := fun x => some (A.exist x)
  explains := TokenReason A
  conjunct := fun g f => g = f

/-- The token together with every old truth at `a`. -/
def tokenAccount (A : Arena W B F) (a : W) : Option F → Prop
  | none => True
  | some f => A.holds a f

/-! ## Rival accounts of one explanandum

All rivals use worlds `Nat`, actual world `0`, universal accessibility and the
explanandum `Fact.target`. They differ in truth assignments and admitted reasons. -/

/-- The fact signature shared by every rival. -/
inductive Fact
  | target
  | other
  | source (i : Bool)
  | member (n : Nat)
  | whole

/-- `none` is the bearer of the target; `some i` is the bearer of source `i`. -/
def beingFact : Option Bool → Fact
  | none => .target
  | some i => .source i

/-- Arena on the shared signature. Causes is empty, so no causal claim is made. -/
def rival (h : Nat → Fact → Prop) (x : Nat → Fact → Fact → Prop) :
    Arena Nat (Option Bool) Fact where
  ontic := {
    frame := ⟨everywhere⟩
    ExistsAt := fun w y => h w (beingFact y)
    Causes := fun _ _ _ => False }
  holds := h
  exist := beingFact
  explains := x
  conjunct := fun g f => g = f

/-- Truth for the source accounts. The target holds at `0` and a rival outcome
holds elsewhere. Source `true` holds everywhere, and source `false` too if `plural`. -/
def groundHolds (plural : Bool) : Nat → Fact → Prop
  | w, .target => w = 0
  | w, .other => w ≠ 0
  | _, .source i => i = true ∨ plural = true
  | _, .member _ => False
  | _, .whole => False

/-- A source that holds is a reason for whichever outcome holds at the world. -/
inductive GroundReason (plural : Bool) : Nat → Fact → Fact → Prop
  | toTarget (i : Bool) : (i = true ∨ plural = true) → GroundReason plural 0 (.source i) .target
  | toOther (i : Bool) (w : Nat) : (i = true ∨ plural = true) → w ≠ 0 →
      GroundReason plural w (.source i) .other

/-- One necessary being whose existence fact is a nonnecessitating reason for the
target. The signature has no predicate for personal agency. -/
def ground : Arena Nat (Option Bool) Fact := rival (groundHolds false) (GroundReason false)

/-- Two independent necessary beings, each a nonnecessitating reason for the target. -/
def plural : Arena Nat (Option Bool) Fact := rival (groundHolds true) (GroundReason true)

/-- The truths and reasons of `ground`, with one contingent being, the target's
bearer. Source `true` is a necessary fact that is no being's existence fact. It may
be read as a necessary law or as a bare token: the arena is the same. -/
def law : Arena Nat Unit Fact where
  ontic := {
    frame := ⟨everywhere⟩
    ExistsAt := fun w _ => w = 0
    Causes := fun _ _ _ => False }
  holds := groundHolds false
  exist := fun _ => .target
  explains := GroundReason false
  conjunct := fun g f => g = f

/-- Truth in the infinite chain. Member `n` holds at `0` and at each `w` above
`n + 2`; the whole holds at `0` alone, and the target everywhere except world `1`. -/
def chainHolds : Nat → Fact → Prop
  | w, .target => w ≠ 1
  | _, .other => False
  | _, .source _ => False
  | w, .member n => w = 0 ∨ n + 2 < w
  | w, .whole => w = 0

/-- Each member is a reason for its predecessor, member `0` for the target, and
every member for the whole. -/
inductive ChainReason : Nat → Fact → Fact → Prop
  | toTarget : ChainReason 0 (.member 0) .target
  | step (n : Nat) : ChainReason 0 (.member (n + 1)) (.member n)
  | toWhole (m : Nat) : ChainReason 0 (.member m) .whole

/-- A source-free infinite history of contingent facts. -/
def chain : Arena Nat (Option Bool) Fact := rival chainHolds ChainReason

/-- Truth in the brute account: source `true` holds at worlds `0` and `1` alone. -/
def bruteHolds : Nat → Fact → Prop
  | w, .target => w = 0
  | _, .other => False
  | w, .source i => i = true ∧ w ≤ 1
  | _, .member _ => False
  | _, .whole => False

/-- The contingent terminus is the target's only reason and has none of its own. -/
inductive BruteReason : Nat → Fact → Fact → Prop
  | step : BruteReason 0 (.source true) .target

/-- A contingent terminus with no reason. -/
def brute : Arena Nat (Option Bool) Fact := rival bruteHolds BruteReason

/-- Truth with a necessary being and a contingent target. -/
def idleHolds : Nat → Fact → Prop
  | w, .target => w = 0
  | _, .other => False
  | _, .source i => i = true
  | _, .member _ => False
  | _, .whole => False

/-- A necessary being exists and no reason is admitted for anything. -/
def idle : Arena Nat (Option Bool) Fact := rival idleHolds (fun _ _ _ => False)

/-- Truth with the target and source `true` at every world. -/
def necessityHolds : Nat → Fact → Prop
  | _, .target => True
  | _, .other => False
  | _, .source i => i = true
  | _, .member _ => False
  | _, .whole => False

/-- The source necessitates the target at every world. -/
inductive NecessityReason : Nat → Fact → Fact → Prop
  | step (w : Nat) : NecessityReason w (.source true) .target

/-- Nothing in the account is contingent: the target's actuality has no rival. -/
def necessitarian : Arena Nat (Option Bool) Fact := rival necessityHolds NecessityReason

/-- The account of `ground`, `law` and `necessitarian`: target and source `true`. -/
inductive OneSource : Fact → Prop
  | target : OneSource .target
  | source : OneSource (.source true)

/-- The account of `plural`: target and both sources. -/
inductive TwoSources : Fact → Prop
  | target : TwoSources .target
  | source (i : Bool) : TwoSources (.source i)

/-- The chain account without the whole: target and all members. -/
inductive Members : Fact → Prop
  | target : Members .target
  | member (n : Nat) : Members (.member n)

/-- The chain account with the whole. -/
inductive MembersAndWhole : Fact → Prop
  | target : MembersAndWhole .target
  | member (n : Nat) : MembersAndWhole (.member n)
  | whole : MembersAndWhole .whole

/-! ## #735 overlays as arenas -/

/-- The exact #735 modal overlay `k, b`. Facts are existence facts of its event
candidates, and a reason for an event is an actual graph contributor to it. -/
def overlay (k : UltimateAdequacy.Kind) (b : Bool) : Arena Bool Nat Nat where
  ontic := UltimateAdequacy.modal k b
  holds := (UltimateAdequacy.modal k b).ExistsAt
  exist := id
  explains := (UltimateAdequacy.modal k b).Causes
  conjunct := fun g f => g = f

/-! ## Certificates -/

/-- The incompatible core and a deletion witness for each member.

First conjunct: no arena has a reason-closed account with a contingent explanandum,
a founded contingent reason relation and only contingent reasons. Second conjunct:
necessitating reasons may replace varying ones. Third: `ContrastRelevant` may replace
them too, since it gives each contingent member some contingent reason. Remaining conjuncts each keep the other members and
refute the deleted one, which certifies inclusion-minimality of the first bundle
(not minimum cardinality, and nothing about the second). The core forces a rejection
of at least one member and chooses none. -/
def Core : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ReasonClosed A a S x → Contingent A a x → Founded A a S → AllReasonsVary A a S → False) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ReasonClosed A a S x → Contingent A a x → Founded A a S →
    AllReasonsNecessitate A a S → False) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ReasonClosed A a S x → Contingent A a x → Founded A a S →
    ContrastRelevant A a S → False) ∧
  -- delete reason closure: the brute terminus
  ((∀ S, ¬ ReasonClosed brute 0 S .target) ∧ Contingent brute 0 .target ∧
    Founded brute 0 OneSource ∧ AllReasonsVary brute 0 OneSource) ∧
  -- delete foundedness: the infinite chain
  (ReasonClosed chain 0 Members .target ∧ Contingent chain 0 .target ∧
    ¬ Founded chain 0 Members ∧ AllReasonsVary chain 0 Members) ∧
  -- delete varying reasons: the necessary nonnecessitating ground
  (ReasonClosed ground 0 OneSource .target ∧ Contingent ground 0 .target ∧
    Founded ground 0 OneSource ∧ ¬ AllReasonsVary ground 0 OneSource) ∧
  -- delete contingency: no rival to the target
  (ReasonClosed necessitarian 0 OneSource .target ∧ ¬ Contingent necessitarian 0 .target ∧
    Founded necessitarian 0 OneSource ∧ AllReasonsVary necessitarian 0 OneSource)

/-- The verdicts of each candidate standard on the shared rivals, with the
non-theistic witnesses, the token expansion, the circular control and #735.

* Reason closure admits `ground`, `plural`, `law`, `chain` and `necessitarian`, and
  no account of the target in `brute` or `idle` meets it.
* Contrast relevance has no account of the target in `ground`, `plural`, `law`,
  `brute` or `idle`, and is met by `chain` and vacuously by `necessitarian`. Uniform
  contrast is met by `chain` without the whole; with the whole, per-rival contrast
  holds and uniform contrast fails.
* Two-way reasons are met by `ground`, `plural`, `law` and vacuously by
  `necessitarian`; no account of the target meets them in `chain`, `brute` or `idle`.
* Reason closure, contrast and two-way reasons cannot see beings: each is equivalent
  on an arena and its `bare` projection, and `ground` and `law` have one projection.
  `law` and `chain` have no necessary being and `idle` has one without closure.
* Token expansion gives any truth of any arena a reason-closed account while truth
  and beings are unchanged, so `brute` goes from no account to one; contrast fails
  for a contingent explanandum, and two-way reasons hold given a rival outcome.
* `BeingStop` is the circular control: `ground` and `plural` meet it, `law` fails it,
  `chain` meets it vacuously. With reason closure, foundedness and a contingent
  explanandum, it excludes that no being is necessary: the premise named the result.
* On the #735 overlays: every graph has a reason-closed account of target2 under the
  all-necessary overlay; under the other overlay `single` and `plural` have one and
  `branch` and `chain` have none. Chain has no joint Supply of target2, and plural
  has Supply with no least node, by #735. -/
def Comparison : Prop :=
  -- reason closure
  ReasonClosed ground 0 OneSource .target ∧ ReasonClosed plural 0 TwoSources .target ∧
  ReasonClosed law 0 OneSource .target ∧ ReasonClosed chain 0 MembersAndWhole .target ∧
  ReasonClosed necessitarian 0 OneSource .target ∧
  (∀ S, ¬ ReasonClosed brute 0 S .target) ∧ (∀ S, ¬ ReasonClosed idle 0 S .target) ∧
  -- contrast relevance
  (∀ S, S .target → ¬ ContrastRelevant ground 0 S) ∧
  (∀ S, S .target → ¬ ContrastRelevant plural 0 S) ∧
  (∀ S, S .target → ¬ ContrastRelevant law 0 S) ∧
  (∀ S, S .target → ¬ ContrastRelevant brute 0 S) ∧
  (∀ S, S .target → ¬ ContrastRelevant idle 0 S) ∧
  ContrastRelevant chain 0 Members ∧ UniformContrast chain 0 Members ∧
  ContrastRelevant chain 0 MembersAndWhole ∧ ¬ UniformContrast chain 0 MembersAndWhole ∧
  ContrastRelevant necessitarian 0 OneSource ∧
  -- two-way reasons
  TwoWay ground 0 OneSource ∧ TwoWay plural 0 TwoSources ∧ TwoWay law 0 OneSource ∧
  TwoWay necessitarian 0 OneSource ∧
  (∀ S, S .target → ¬ TwoWay chain 0 S) ∧
  (∀ S, S .target → ¬ TwoWay brute 0 S) ∧
  (∀ S, S .target → ¬ TwoWay idle 0 S) ∧
  -- these standards do not read beings; necessary beings neither needed nor sufficient
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    (ReasonClosed A a S x ↔ ReasonClosed (bare A) a S x) ∧
    (ContrastRelevant A a S ↔ ContrastRelevant (bare A) a S) ∧
    (TwoWay A a S ↔ TwoWay (bare A) a S)) ∧
  bare ground = bare law ∧
  (∀ x, ¬ NecessaryAt law.ontic 0 x) ∧ (∀ x, ¬ NecessaryAt chain.ontic 0 x) ∧
  NecessaryAt idle.ontic 0 (some true) ∧ NecessaryAt ground.ontic 0 (some true) ∧
  -- token expansion
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (x : F), A.holds a x →
    (tokenExpand A).ontic = A.ontic ∧ (∀ w f, (tokenExpand A).holds w (some f) ↔ A.holds w f) ∧
    ReasonClosed (tokenExpand A) a (tokenAccount A a) (some x)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (x : F) (S : Option F → Prop),
    S (some x) → Contingent A a x → ¬ ContrastRelevant (tokenExpand A) a S) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W),
    (∀ f v, Contingent A a f → Access A a v → ¬ A.holds v f →
      ∃ g, A.holds v g ∧ ¬ A.holds a g ∧ Contingent A v g) →
    TwoWay (tokenExpand A) a (tokenAccount A a)) ∧
  ReasonClosed (tokenExpand brute) 0 (tokenAccount brute 0) (some .target) ∧
  -- the circular control
  BeingStop ground 0 OneSource ∧ BeingStop plural 0 TwoSources ∧
  (∀ S, ReasonClosed law 0 S .target → ¬ BeingStop law 0 S) ∧
  BeingStop chain 0 Members ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (S : F → Prop) (x : F),
    ReasonClosed A a S x → Contingent A a x → Founded A a S → BeingStop A a S →
    ¬ ∀ y, ¬ NecessaryAt A.ontic a y) ∧
  -- #735 overlays
  (∀ k, ∃ S, ReasonClosed (overlay k true) false S 2) ∧
  (∃ S, ReasonClosed (overlay .single false) false S 2) ∧
  (∃ S, ReasonClosed (overlay .plural false) false S 2) ∧
  (∀ S, ¬ ReasonClosed (overlay .branch false) false S 2) ∧
  (∀ S, ¬ ReasonClosed (overlay .chain false) false S 2) ∧
  ¬ TruthCore.Causality.DerivativeJointPower.Supply
    (UltimateAdequacy.groups .chain) (UltimateAdequacy.intrinsic .chain) 2 ∧
  TruthCore.Causality.DerivativeJointPower.Supply
    (UltimateAdequacy.groups .plural) (UltimateAdequacy.intrinsic .plural) 2 ∧
  ¬ (∃ s, TruthCore.Causality.JointGroups.least (UltimateAdequacy.groups .plural).graph s)

end TruthCore.Explanation.ExplanatoryAdequacy
