import TruthCore.Explanation.PSRStrength
import TruthCore.Logic.SelfApplication

/-!
# Applying the demand for reasons to one's own stance (#756)

`PSRStrength.Arena.explains w r f` is ontic: at `w`, `r` is admitted as a reason why
`f` obtains. `Inquiry.supports w e p` is epistemic: at `w`, `e` is admitted as a
reason to accept `p`. Neither relation is defined from the other. Smoke is a reason
to accept that there is a fire and is no reason why there is one; a cause nobody has
noticed is a reason why, and gives nobody a reason to accept anything. A `Stance`
records what someone accepts, what is core to their position, and which claims they
subject to the epistemic demand.

Every model below is an analyst-built structure over stipulated relations. It shows
that a formal bundle is satisfiable. It does not show that the evidence in it is
good, that the bundle is metaphysically possible, or that any person holds it. See
`docs/notes/psr-self-application-756.md` for the interpretation and the limits.
-/
namespace TruthCore.Explanation.PSRSelfApplication

open TruthCore.Explanation.PSRStrength
open TruthCore.Logic.SelfApplication

/-! ## The epistemic layer -/

/-- `supports w e p`: at `w`, `e` is admitted as a reason to accept `p`. It is an
interpreted parameter. It is not assumed factive, transitive, asymmetric or
well-founded, and it says nothing about why `p` obtains. -/
structure Inquiry (W F : Type) where
  supports : W → F → F → Prop

/-- Some fact is admitted as a reason to accept `p` at `w`. -/
def Supported {W F : Type} (I : Inquiry W F) (w : W) (p : F) : Prop :=
  ∃ e, I.supports w e p

/-- What a stance accepts, what is core to it, and which claims it subjects to the
demand that accepting them requires a reason. Being demanded is a commitment of the
stance, not a fact about the claim. -/
structure Stance (F : Type) where
  accepts : F → Prop
  core : F → Prop
  demands : F → Prop

variable {W B F : Type}

/-- The stance's demand as an instance of the #397 norm schema: scope is what the
stance demands, standard is having a supporting reason at `w`. -/
def demandNorm (S : Stance F) (I : Inquiry W F) (w : W) : Norm F :=
  ⟨S.demands, Supported I w⟩

/-- The stance meets its own demand at `w`: everything it both demands and accepts
is supported. -/
def Honors (S : Stance F) (I : Inquiry W F) (w : W) : Prop :=
  (demandNorm S I w).Holds S.accepts

/-- "No belief needs justification." -/
def NoneDemanded (S : Stance F) : Prop := ∀ p, ¬ S.demands p

/-- "Every core commitment needs a reason." A commitment of the stance only. -/
def CoreDemanded (S : Stance F) : Prop := ∀ p, S.core p → S.demands p

/-- Every accepted claim is supported by some accepted claim at `w`. -/
def EveryAcceptedBacked (S : Stance F) (I : Inquiry W F) (w : W) : Prop :=
  ∀ p, S.accepts p → ∃ e, S.accepts e ∧ I.supports w e p

/-- Evidence is true where it is used. The supported claim need not be. -/
def EvidenceTrue (A : Arena W B F) (I : Inquiry W F) : Prop :=
  ∀ w e p, I.supports w e p → A.holds w e

/-! ## The three standings of an exemption -/

/-- Demanding reasons for `target` and for `own`. -/
def Uniform (S : Stance F) (target own : F) : Prop :=
  S.demands target ∧ S.demands own

/-- Demanding reasons for `target` and not for `own`, which agree on the feature
`k`. This is an asymmetry relative to `k`, not a contradiction. -/
def Selective (S : Stance F) (k : F → Prop) (target own : F) : Prop :=
  S.demands target ∧ ¬ S.demands own ∧ (k target ↔ k own)

/-- Demanding reasons for `target` and not for `own`, which differ on the feature
`k`. This records that `k` draws the line, not that `k` is a defensible line. -/
def Restricted (S : Stance F) (k : F → Prop) (target own : F) : Prop :=
  S.demands target ∧ ¬ S.demands own ∧ ¬ (k target ↔ k own)

/-! ## Ontic scope -/

/-- `f` is a contingent truth at `w` with no reason at `w`. -/
def BruteAt (A : Arena W B F) (w : W) (f : F) : Prop :=
  Contingent A w f ∧ ¬ Explained A w f

/-- The contingent-fact PSR restricted to the domain `D`. -/
def RestrictedPSR (A : Arena W B F) (w : W) (D : F → Prop) : Prop :=
  ∀ f, D f → Contingent A w f → Explained A w f

/-- The fact `c` is true exactly where the contingent-fact PSR holds. -/
def TracksPSR (A : Arena W B F) (c : F) : Prop :=
  ∀ v, A.holds v c ↔ ContingentPSR A v

/-- The fact `c` is true exactly where some contingent truth has no reason. -/
def TracksRejection (A : Arena W B F) (c : F) : Prop :=
  ∀ v, A.holds v c ↔ ∃ f, BruteAt A v f

/-! ## Epistemic-to-ontic bridges -/

/-- Whatever contingent truth is supported at `w` has a reason at `w`. -/
def TrackingBridge (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  ∀ f, Contingent A w f → Supported I w f → Explained A w f

/-- Every contingent truth is supported at `w`. -/
def SupportCoverage (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  ∀ f, Contingent A w f → Supported I w f

/-- A contingent truth used at `w` as evidence has a reason at `w`. It constrains
evidence only. A fact that is only ever supported is outside it. -/
def EvidenceBridge (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  ∀ e p, I.supports w e p → Contingent A w e → Explained A w e

/-- If some accessible world has a brute contingent truth, nothing supports anything
at `w`. This conditional says nothing about whether such a world exists. -/
def GlobalDefeat (A : Arena W B F) (I : Inquiry W F) (w : W) : Prop :=
  (∃ v f, Access A w v ∧ BruteAt A v f) → ¬ ∃ e p, I.supports w e p

/-! ## The scene: one signature for the models -/

/-- Worlds of the scene. -/
inductive Scene | a | b | c

/-- Facts of the scene. `root` is the candidate brute foundation, `event` the
observed effect, `alt` the only ordinary fact of world `c`, `psr` and `rejection` the
two general claims. -/
inductive Fact | root | event | alt | psr | rejection

/-- A table over the facts, in the order root, event, alt, psr, rejection. Written
without a wildcard, because a wildcard match would bring in `propext`. -/
def tbl {α : Type} (root event alt psr rejection : α) : Fact → α
  | .root => root
  | .event => event
  | .alt => alt
  | .psr => psr
  | .rejection => rejection

/-- A table with `false` everywhere. -/
def none₀ : Fact → Bool := tbl false false false false false

/-- `root` is true only at `a`, `event` at `a` and `b`, `alt` only at `c`. In the
scene every world has a brute truth, so `psr` is true nowhere and `rejection`
everywhere. That is a feature of this structure, not a thesis. -/
def sceneHolds : Scene → Fact → Bool
  | .a => tbl true true false false true
  | .b => tbl false true false false true
  | .c => tbl false false true false true

/-- With `hasLocal := true`, the root is a reason for the event at `a`. There are no
other reasons. -/
def sceneLink (hasLocal : Bool) : Scene → Fact → Fact → Bool
  | .a => tbl (tbl false hasLocal false false false) none₀ none₀ none₀ none₀
  | .b => tbl none₀ none₀ none₀ none₀ none₀
  | .c => tbl none₀ none₀ none₀ none₀ none₀

/-- The scene arena. `scene false` removes the one local reason. -/
def scene (hasLocal : Bool) : Arena Scene Empty Fact :=
  basic everywhere (fun w f => sceneHolds w f = true)
    (fun w r f => sceneLink hasLocal w r f = true)
    (fun g f => g = f)

/-- An inquiry in the scene, with supports only at world `a`. -/
def edges (g : Fact → Fact → Bool) : Inquiry Scene Fact :=
  ⟨fun w e p => w = .a ∧ g e p = true⟩

/-- No support at all. -/
def blank : Inquiry Scene Fact := edges fun _ _ => false

/-- The observed event supports the root, by inference from effect to candidate
explanation, and supports the rejection claim. Stipulated edges: nothing here says
that such an inference is cogent. -/
def science : Inquiry Scene Fact :=
  edges (tbl none₀ (tbl true false false false true) none₀ none₀ none₀)

/-- As `science`, except that the root is used as evidence for the rejection claim. -/
def premiseRoot : Inquiry Scene Fact :=
  edges (tbl (tbl false false false false true) (tbl true false false false false)
    none₀ none₀ none₀)

/-- A two-claim circle of support. -/
def loop : Inquiry Scene Fact :=
  edges (tbl (tbl false true false false false) (tbl true false false false false)
    none₀ none₀ none₀)

/-- The event supports the claim `psr`. Stipulated. -/
def defense : Inquiry Scene Fact :=
  edges (tbl none₀ (tbl false false false true false) none₀ none₀ none₀)

/-- A stance in the scene, from three membership tests. -/
def stance (acc cor dem : Fact → Bool) : Stance Fact :=
  ⟨fun p => acc p = true, fun p => cor p = true, fun p => dem p = true⟩

/-- Accepted by the critics: root, event, rejection. -/
def criticAccepts : Fact → Bool := tbl true true false false true

/-- Core to the critics: root and rejection. The observed event is not core. -/
def criticCore : Fact → Bool := tbl true false false false true

/-- Demands reasons for the claim `psr` and for its own core commitments. -/
def critic : Stance Fact :=
  stance criticAccepts criticCore (tbl true false false true true)

/-- Same acceptances and core as `critic`; demands reasons for the claim `psr` only. -/
def selective : Stance Fact :=
  stance criticAccepts criticCore (tbl false false false true false)

/-- Demands nothing. -/
def silent : Stance Fact := stance criticAccepts criticCore none₀

/-- Accepts the root, holds nothing core, and demands reasons for the claim `psr`. -/
def nonCore : Stance Fact :=
  stance criticAccepts none₀ (tbl false false false true false)

/-- The critic's core and demands with nothing accepted. -/
def noAccept : Stance Fact :=
  stance none₀ criticCore (tbl true false false true true)

/-- Accepts root and event, for the circle of support. -/
def loopStance : Stance Fact :=
  stance (tbl true true false false false) none₀ none₀

/-- Accepts the event and the claim `psr`, holds `psr` core and demands it. -/
def defender : Stance Fact :=
  stance (tbl false true false true false) (tbl false false false true false)
    (tbl false false false true false)

/-- Features under which `selective` is compared. `commitment` counts the root and
the claim `psr` alike; `generalLaw` holds of the claim `psr` alone. Neither is
defended here as the right feature. -/
def commitment : Fact → Prop := tbl True False False True True

/-- See `commitment`. -/
def generalLaw : Fact → Prop := tbl False False False True False

/-- An endless chain of support: each number is supported by its successor, and all
are accepted. -/
def chain : Inquiry Unit Nat := ⟨fun _ e p => e = p + 1⟩

/-- Accepts every number; demands nothing and holds nothing core. -/
def chainStance : Stance Nat := ⟨fun _ => True, fun _ => False, fun _ => False⟩

/-- The ground supports the choice. Stipulated, for the no-brute control. -/
def groundInquiry : Inquiry Bool GroundFact := ⟨fun _ e p => e = .ground ∧ p = .choice⟩

/-! ## Certificates -/

/-- **What the self-application charge can and cannot convict.**

* The stated-rule contradictions: "no belief needs justification" cannot stand with a
  demand. "Every core commitment needs a reason", meeting one's demands, and an
  accepted core commitment with no support cannot stand together; each of those five
  members is deleted by a named scene stance and inquiry.
* The #397 schema applied to a demanded unsupported claim.
* A checked three-way fork for a demanded target: uniform, selective, restricted. It is
  exhaustive given decidability of the demand and of the feature comparison, and the
  standings exclude each other outright.
* A named consistent critic at world `a`: it demands reasons for the claim `psr` and
  for its own core commitments and meets them, its root is supported and brute, and the
  event has a reason and no support. `rejection` and `psr` track their contents at every
  world of the scene.
* One stance is selective relative to one feature and restricted relative to another.
* A boundary defined by having a reason constrains no arena; a status can always be
  made its own feature; the event-scoped boundary holds with the local reason and
  fails without it.
* No stance, whatever it says about the PSR, has at one world every accepted claim
  backed by an accepted claim, well-founded support and something accepted. Each of
  the three is deleted by a named model; the circle and the endless chain both delete
  well-foundedness.
* The named `defender` honors the demand for the claim `psr` where that claim is
  false. -/
def StanceMap : Prop :=
  -- stated-rule contradictions
  (∀ (F : Type) (S : Stance F) (p : F), NoneDemanded S → S.demands p → False) ∧
  (NoneDemanded silent ∧ ¬ silent.demands .psr ∧ critic.demands .psr ∧ ¬ NoneDemanded critic) ∧
  (∀ (W F : Type) (S : Stance F) (I : Inquiry W F) (w : W) (b : F),
    CoreDemanded S → Honors S I w → S.core b → S.accepts b → ¬ Supported I w b → False) ∧
  -- five deletions, each at the root and world `a`
  (¬ CoreDemanded selective ∧ Honors selective blank .a ∧ selective.core .root ∧
    selective.accepts .root ∧ ¬ Supported blank .a .root) ∧
  (CoreDemanded critic ∧ ¬ Honors critic blank .a ∧ critic.core .root ∧
    critic.accepts .root ∧ ¬ Supported blank .a .root) ∧
  (CoreDemanded nonCore ∧ Honors nonCore blank .a ∧ ¬ nonCore.core .root ∧
    nonCore.accepts .root ∧ ¬ Supported blank .a .root) ∧
  (CoreDemanded noAccept ∧ Honors noAccept blank .a ∧ noAccept.core .root ∧
    ¬ noAccept.accepts .root ∧ ¬ Supported blank .a .root) ∧
  (CoreDemanded critic ∧ Honors critic science .a ∧ critic.core .root ∧
    critic.accepts .root ∧ Supported science .a .root) ∧
  -- the schema of #397
  (∀ (W F : Type) (S : Stance F) (I : Inquiry W F) (w : W) (b : F),
    S.demands b → ¬ Supported I w b →
      (Honors S I w → ¬ S.accepts b) ∧
      (S.accepts b → (demandNorm S I w).Counterexample S.accepts b)) ∧
  -- the fork
  (∀ (F : Type) (S : Stance F) (k : F → Prop) (target own : F),
    (S.demands own ∨ ¬ S.demands own) → ((k target ↔ k own) ∨ ¬ (k target ↔ k own)) →
    S.demands target →
      Uniform S target own ∨ Selective S k target own ∨ Restricted S k target own) ∧
  (∀ (F : Type) (S : Stance F) (k : F → Prop) (target own : F),
    ¬ (Uniform S target own ∧ Selective S k target own) ∧
    ¬ (Uniform S target own ∧ Restricted S k target own) ∧
    ¬ (Selective S k target own ∧ Restricted S k target own)) ∧
  -- the consistent critic at world `a`
  (Factive (scene true) ∧ Necessitating (scene true) ∧ ReasonIndependent (scene true) ∧
    IrreflexiveContingent (scene true) ∧ EvidenceTrue (scene true) science ∧
    TracksPSR (scene true) .psr ∧ TracksRejection (scene true) .rejection ∧
    CoreDemanded critic ∧ Honors critic science .a ∧ critic.demands .psr ∧
    ¬ critic.accepts .psr ∧ critic.accepts .root ∧ critic.accepts .rejection ∧
    BruteAt (scene true) .a .root ∧ ¬ NoBrute (scene true) .a ∧
    Supported science .a .root ∧ Supported science .a .rejection ∧
    Explained (scene true) .a .event ∧ ¬ Supported science .a .event ∧
    (scene true).explains .a .root .event ∧ science.supports .a .event .root ∧
    ¬ (scene true).explains .a .event .root ∧ ¬ science.supports .a .root .event) ∧
  -- one stance, two features
  (Honors selective science .a ∧ Selective selective commitment .psr .root ∧
    Restricted selective generalLaw .psr .root ∧ selective.core .root) ∧
  -- boundaries
  (∀ (W B F : Type) (A : Arena W B F) (w : W), RestrictedPSR A w (Explained A w)) ∧
  (∀ (F : Type) (d : F → Prop), ∃ k : F → Prop, ∀ f g, (k f ↔ k g) → (d f ↔ d g)) ∧
  (RestrictedPSR (scene false) .a (Explained (scene false) .a) ∧
    ¬ RestrictedPSR (scene false) .a (· = .event) ∧
    RestrictedPSR (scene true) .a (· = .event) ∧
    ¬ RestrictedPSR (scene true) .a (· = .root)) ∧
  -- the epistemic regress core, and its deletions
  (∀ (W F : Type) (S : Stance F) (I : Inquiry W F) (w : W),
    EveryAcceptedBacked S I w → WellFounded (I.supports w) → (∃ p, S.accepts p) → False) ∧
  (¬ EveryAcceptedBacked critic science .a ∧ WellFounded (science.supports .a) ∧
    critic.accepts .root) ∧
  (EveryAcceptedBacked loopStance loop .a ∧ ¬ WellFounded (loop.supports .a) ∧
    loopStance.accepts .root ∧ ∀ e, ¬ loop.supports .a e e) ∧
  (EveryAcceptedBacked chainStance chain () ∧ ¬ WellFounded (chain.supports ()) ∧
    chainStance.accepts 0 ∧ ∀ e p, chain.supports () e p → p < e) ∧
  (EveryAcceptedBacked noAccept science .a ∧ WellFounded (science.supports .a) ∧
    ∀ p, ¬ noAccept.accepts p) ∧
  -- honoring the demand for the claim `psr` where it is false
  (CoreDemanded defender ∧ Honors defender defense .a ∧ defender.accepts .psr ∧
    Supported defense .a .psr ∧ EvidenceTrue (scene true) defense ∧
    ¬ (scene true).holds .a .psr ∧ ¬ ContingentPSR (scene true) .a)

/-- **Which epistemic premise would reach the ontic thesis, and at what cost.**

* Scoped bridges: a scope that excludes a brute truth must contain it, and a scope
  that holds and contains `b` gives the scope holding `b` alone.
* `TrackingBridge` excludes a supported brute truth, follows from `ContingentPSR`, and
  under `SupportCoverage` gives it back, so it is the PSR over the supported facts.
  Without coverage it can hold where the PSR fails.
* `EvidenceBridge` follows from `ContingentPSR`, and forbids using a brute truth as
  evidence. It is neither implied by honoring the demand (`premiseRoot`) nor does it
  give the PSR or exclude a brute truth that is only ever supported (`science`).
* `GlobalDefeat` with some support at `w` gives `NoBrute` at every accessible world.
  It convicts a stance that accepts and demands a claim and honors its demand, if a
  brute truth is accessible. Each of the three members of its core is deleted.
  At a self-accessible world, with any support, it cannot hold with the other members of
  the #755 collapse core.
* The same tests for a necessary ground: a necessary truth that necessitatingly
  explains excludes contingency of its target; `ground true` keeps a contingent target
  without necessitation; `ground false` has the contingent-fact PSR with an unexplained
  necessary ground, so it fails `FactPSR` as the scene does. -/
def BridgeLadder : Prop :=
  -- scoped bridges
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (D : F → Prop) (b : F),
    BruteAt A w b → RestrictedPSR A w D → ¬ D b) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (D : F → Prop) (b : F),
    RestrictedPSR A w D → D b → RestrictedPSR A w (· = b)) ∧
  -- tracking
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W) (b : F),
    TrackingBridge A I w → BruteAt A w b → ¬ Supported I w b) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    ContingentPSR A w → TrackingBridge A I w) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    SupportCoverage A I w → TrackingBridge A I w → ContingentPSR A w) ∧
  (TrackingBridge (scene true) blank .a ∧ ¬ ContingentPSR (scene true) .a ∧
    ¬ TrackingBridge (scene true) science .a) ∧
  -- evidence
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    ContingentPSR A w → EvidenceBridge A I w) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W) (b p : F),
    EvidenceBridge A I w → BruteAt A w b → ¬ I.supports w b p) ∧
  (EvidenceBridge (scene true) science .a ∧ BruteAt (scene true) .a .root ∧
    Supported science .a .root ∧ ¬ ContingentPSR (scene true) .a) ∧
  (CoreDemanded critic ∧ Honors critic premiseRoot .a ∧ EvidenceTrue (scene true) premiseRoot ∧
    premiseRoot.supports .a .root .rejection ∧ ¬ EvidenceBridge (scene true) premiseRoot .a) ∧
  -- global defeat
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W) (e p : F),
    GlobalDefeat A I w → I.supports w e p → ∀ v, Access A w v → NoBrute A v) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (S : Stance F) (w v : W) (f c : F),
    GlobalDefeat A I w → Access A w v → BruteAt A v f →
    S.demands c → S.accepts c → Honors S I w → False) ∧
  (¬ GlobalDefeat (scene true) science .a ∧ BruteAt (scene true) .a .root ∧
    science.supports .a .event .root) ∧
  (GlobalDefeat (ground true) groundInquiry false ∧
    groundInquiry.supports false .ground .choice ∧
    (∀ v, NoBrute (ground true) v) ∧ Contingent (ground true) false .choice) ∧
  (GlobalDefeat (scene true) blank .a ∧ BruteAt (scene true) .a .root ∧
    ¬ ∃ e p, blank.supports .a e p) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (a : W) (e p t c : F),
    GlobalDefeat A I a → I.supports a e p → Access A a a →
    ConjunctSound A → Factive A → Necessitating A → Distribution A →
    IrreflexiveContingent A → BCCFAt A a t → Contingent A a c → False) ∧
  -- the necessary ground under the same tests
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (r f : F),
    Necessitating A → (∀ v, Access A w v → A.holds v r) → A.explains w r f →
    ¬ Contingent A w f) ∧
  (¬ Necessitating (ground true) ∧ Contingent (ground true) false .choice ∧
    (ground true).explains false .ground .choice ∧ ∀ v, (ground true).holds v .ground) ∧
  (ContingentPSR (ground false) false ∧ (∀ v, (ground false).holds v .ground) ∧
    ¬ Explained (ground false) false .ground ∧ ¬ FactPSR (ground false) false ∧
    ¬ FactPSR (scene true) .a)

end TruthCore.Explanation.PSRSelfApplication
