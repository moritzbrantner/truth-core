import TruthCore.Explanation.ExistencePSR

/-!
# A common arena for strengths of the Principle of Sufficient Reason (#755)

One typed vocabulary in which PSR formulations differ only by an explicit scope,
modal position or quality condition. `Arena.explains w r f` is read: at world `w`,
the fact `r` is admitted as a reason why the fact `f` obtains. The relation is an
interpreted parameter, not a theory of explanation. It is not assumed causal,
transitive, asymmetric, well-founded, contrastive or necessitating; each such
condition is either a separate named hypothesis or absent. See
`docs/notes/psr-strength-755.md` for the interpretation, the strength table and
the open bridges.

Models below are analyst-built mathematical interpretations. A model shows that a
formal bundle is satisfiable, not that it is metaphysically possible. Theorems
establish conditional consequence, not the truth of any PSR.
-/
namespace TruthCore.Explanation.PSRStrength

open TruthCore.German.Kant.CosmologicalInference

/-- The comparison arena. `ontic` reuses the existing world, accessibility,
existence and causal vocabulary. Facts are a separate sort from beings: `exist x`
is the fact that `x` exists, and other facts need not concern existence. Reasons
are facts, so that a reason can itself be contingent and can itself belong to a
totality; #312's reason tokens embed through `ofModel` below.
`conjunct g f` records that `g` is a part of the aggregate fact `f`. -/
structure Arena (W B F : Type) where
  ontic : Ontic W B
  holds : W → F → Prop
  exist : B → F
  explains : W → F → F → Prop
  conjunct : F → F → Prop

variable {W B F : Type}

/-- `v` is accessible from `w`. -/
def Access (A : Arena W B F) (w v : W) : Prop := A.ontic.frame.access w v

/-- True here and false at some accessible world. -/
def Contingent (A : Arena W B F) (w : W) (f : F) : Prop :=
  A.holds w f ∧ ∃ v, Access A w v ∧ ¬ A.holds v f

/-- Some fact is admitted as a reason for `f` at `w`. -/
def Explained (A : Arena W B F) (w : W) (f : F) : Prop := ∃ r, A.explains w r f

/-! ## Formulations: scope -/

/-- Unrestricted fact PSR at `w`: every fact true there has a reason. -/
def FactPSR (A : Arena W B F) (w : W) : Prop :=
  ∀ f, A.holds w f → Explained A w f

/-- Actual contingent-fact PSR at `w`. -/
def ContingentPSR (A : Arena W B F) (w : W) : Prop :=
  ∀ f, Contingent A w f → Explained A w f

/-- Existence PSR at `w`: every existent's existence fact has a reason. -/
def ExistencePSR (A : Arena W B F) (w : W) : Prop :=
  ∀ x, A.ontic.ExistsAt w x → Explained A w (A.exist x)

/-- No contingent truth at `w` lacks a reason. This negative form is what the
incompatible core needs; `ContingentPSR` gives it without excluded middle. -/
def NoBrute (A : Arena W B F) (w : W) : Prop :=
  ¬ ∃ f, Contingent A w f ∧ ¬ Explained A w f

/-- Every existent at `w` has a distinct existing efficient cause. Causation
stays the separate `Ontic.Causes` relation. -/
def ExternalCause (A : Arena W B F) (w : W) : Prop :=
  ∀ x, A.ontic.ExistsAt w x → ∃ y, A.ontic.ExistsAt w y ∧ y ≠ x ∧ A.ontic.Causes w y x

/-! ## Formulations: modal position -/

/-- Necessity of the contingent-fact PSR: it holds at every accessible world. -/
def NecessaryPSR (A : Arena W B F) (w : W) : Prop :=
  ∀ v, Access A w v → ContingentPSR A v

/-- Weak PSR: each contingent truth possibly has a reason, at an accessible
world where it is true. The reason need not obtain, or explain, at `w`. -/
def WeakPSR (A : Arena W B F) (w : W) : Prop :=
  ∀ f, Contingent A w f → ∃ v, Access A w v ∧ A.holds v f ∧ Explained A v f

/-- One reason for `f` that serves at every world where `f` is true (`∃ r □`,
as against the world-relative `□ ∃ r` of `ExistencePSR` at every world). -/
def StableReason (A : Arena W B F) (f : F) : Prop :=
  ∃ r, ∀ w, A.holds w f → A.explains w r f

/-! ## Formulations: plurality -/

/-- `t` is an aggregate candidate for the Big Conjunctive Contingent Fact at `w`:
it is true there and has every contingent truth of `w` as a conjunct. Nothing
says that every domain of facts contains such a `t`. -/
def BCCFAt (A : Arena W B F) (w : W) (t : F) : Prop :=
  A.holds w t ∧ ∀ q, Contingent A w q → A.conjunct q t

/-- One reason serves for every contingent truth at `w`, member by member. This
is a common reason, not a reason for a newly reified whole. -/
def CommonReason (A : Arena W B F) (w : W) : Prop :=
  ∃ r, ∀ f, Contingent A w f → A.explains w r f

/-! ## Formulations: quality of the reason -/

/-- Reasons and explananda are true at the world of the explanation. -/
def Factive (A : Arena W B F) : Prop :=
  ∀ w r f, A.explains w r f → A.holds w r ∧ A.holds w f

/-- A reason's truth modally suffices for what it explains. This is the extra
commitment that a sufficient reason need not carry. -/
def Necessitating (A : Arena W B F) : Prop :=
  ∀ w r f, A.explains w r f → ∀ v, Access A w v → A.holds v r → A.holds v f

/-- A reason for a contingent fact is not modally coextensive with it. A reason
that merely copies its target fails this. -/
def ReasonIndependent (A : Arena W B F) : Prop :=
  ∀ w r f, A.explains w r f → Contingent A w f →
    ¬ ∀ v, Access A w v → (A.holds v r ↔ A.holds v f)

/-- A reason for an aggregate is a reason for each of its conjuncts. -/
def Distribution (A : Arena W B F) : Prop :=
  ∀ w r f g, A.explains w r f → A.conjunct g f → A.explains w r g

/-- No contingent fact is a reason for itself. Necessary self-explanation is
deliberately not excluded. -/
def IrreflexiveContingent (A : Arena W B F) : Prop :=
  ∀ w r, Contingent A w r → ¬ A.explains w r r

/-! ## Background laws and domain bridges -/

/-- A conjunct is true wherever its aggregate is true. -/
def ConjunctSound (A : Arena W B F) : Prop :=
  ∀ g f v, A.conjunct g f → A.holds v f → A.holds v g

/-- `exist x` is true exactly where `x` exists. -/
def Coherent (A : Arena W B F) : Prop :=
  ∀ w x, A.holds w (A.exist x) ↔ A.ontic.ExistsAt w x

/-- The domain has, for each brute contingent truth `f` at `w`, a fact about
explanation: "`f`, and `f` has no reason". The weak-to-strong bridge needs it. -/
def UnexplainedFacts (A : Arena W B F) (w : W) : Prop :=
  ∀ f, Contingent A w f → ¬ Explained A w f →
    ∃ u, A.conjunct f u ∧ ∀ v, A.holds v u ↔ (A.holds v f ∧ ¬ Explained A v f)

/-- Coarse-grained domain: every set of worlds is the extension of some fact. -/
def Extensional (A : Arena W B F) : Prop :=
  ∀ P : W → Prop, ∃ f, ∀ v, A.holds v f ↔ P v

/-- Being a conjunct coincides with being entailed at every world. -/
def EntailmentConjunct (A : Arena W B F) : Prop :=
  ∀ g f, A.conjunct g f ↔ ∀ v, A.holds v f → A.holds v g

/-! ## Models -/

/-- A world and fact signature with no beings, when existence plays no role. -/
def basic (access : W → W → Prop) (holds : W → F → Prop)
    (explains : W → F → F → Prop) (conjunct : F → F → Prop) : Arena W Empty F where
  ontic := {
    frame := ⟨access⟩
    ExistsAt := fun _ x => x.elim
    Causes := fun _ x _ => x.elim }
  holds := holds
  exist := fun x => x.elim
  explains := explains
  conjunct := conjunct

/-- Universal accessibility, used by every model except `nonReflexive`. -/
def everywhere (_ _ : W) : Prop := True

/-- Facts of the brute-terminus negative control. -/
inductive TerminusFact | terminus | effect | whole

/-- Negative control: a contingent terminus reasons for its effect and nothing
reasons for the terminus or for the whole. -/
def bruteTerminus : Arena Bool Empty TerminusFact :=
  basic everywhere (fun w _ => w = false)
    (fun w r f => match r, f with
      | .terminus, .effect => w = false
      | .terminus, .terminus => False
      | .terminus, .whole => False
      | .effect, .terminus => False
      | .effect, .effect => False
      | .effect, .whole => False
      | .whole, .terminus => False
      | .whole, .effect => False
      | .whole, .whole => False)
    (fun g f => match g, f with
      | .terminus, .terminus => True
      | .terminus, .effect => False
      | .terminus, .whole => True
      | .effect, .terminus => False
      | .effect, .effect => True
      | .effect, .whole => True
      | .whole, .terminus => False
      | .whole, .effect => False
      | .whole, .whole => True)

/-- `true` is a contingent fact, `false` a reason token that is never true. It
explains without obtaining, so it deletes factivity alone. -/
def falseToken : Arena Bool Empty Bool :=
  basic everywhere (fun w f => f = true ∧ w = false)
    (fun _ r f => r = false ∧ f = true)
    (fun g f => g = f)

/-- Individuals and facts of the necessary-ground control. -/
inductive GroundFact | ground | choice

/-- Positive control: a necessary ground and a contingent choice, with the ground
as nonnecessitating reason for each true fact; `self` says whether it also reasons
for itself. The signature has no predicate for personal agency: a necessary
personal ground with free choice and a necessary impersonal ground with an
indeterministic output are the same structure here, and no theorem separates them. -/
def ground (self : Bool) : Arena Bool GroundFact GroundFact where
  ontic := {
    frame := ⟨everywhere⟩
    ExistsAt := fun w x => match x with
      | .ground => True
      | .choice => w = false
    Causes := fun w y x => match y, x with
      | .ground, .choice => w = false
      | .ground, .ground => False
      | .choice, .ground => False
      | .choice, .choice => False }
  holds := fun w f => match f with
    | .ground => True
    | .choice => w = false
  exist := id
  explains := fun w r f => match r, f with
    | .ground, .choice => w = false
    | .ground, .ground => self = true
    | .choice, .ground => False
    | .choice, .choice => False
  conjunct := fun g f => g = f

/-- Facts are finite exclusion lists: `l` is true at every world not on `l`, so
facts have cofinite extensions. The domain is closed under finite conjunction and
has no infinite conjunction. A reason for `f` is a strictly stronger true list. -/
def cofinite : Arena Nat Empty (List Nat) :=
  basic everywhere (fun k l => k ∉ l)
    (fun k r f => k ∉ r ∧ (∀ y, y ∈ f → y ∈ r) ∧ ∃ x, x ∈ r ∧ x ∉ f)
    (fun g f => ∀ y, y ∈ g → y ∈ f)

/-- `false` and `true` name two coextensive contingent facts, the fact and the
aggregate, each a reason for the other. Mutual explanation is admitted because no
asymmetry is assumed; this model deletes distribution alone. -/
def mutualReasons : Arena Bool Empty Bool :=
  basic everywhere (fun w _ => w = false)
    (fun w r f => w = false ∧ r ≠ f)
    (fun g f => f = true ∨ g = f)

/-- One contingent fact that is its own reason. Minimal target copy. -/
def selfWhole : Arena Bool Empty Unit :=
  basic everywhere (fun w _ => w = false) (fun w _ _ => w = false) (fun _ _ => True)

/-- Positive control: `false` is a necessary ground that necessitates the
necessary `true`. No contingency exists, so the core has nothing to refute. -/
def allNecessary : Arena Bool Empty Bool :=
  basic everywhere (fun _ _ => True) (fun _ r _ => r = false) (fun _ _ => True)

/-- Worlds of the infinite-history family. `lawful` and `rogue` contain the whole
history; `cut k` contains only the members below `k`. The law holds only at `lawful`. -/
inductive HistoryWorld
  | lawful
  | rogue
  | cut (k : Nat)

/-- Facts of the infinite-history family. -/
inductive HistoryFact
  | member (n : Nat)
  | hist
  | law

/-- Each later member's fact is a reason for the earlier one. With `withLaw` the
law is also a reason for the whole history and for each member. No model has a
reason for the law. -/
def historyLink (withLaw : Bool) : HistoryFact → HistoryFact → Prop
  | .member m, .member n => m = n + 1
  | .member _, .hist => False
  | .member _, .law => False
  | .hist, .member _ => False
  | .hist, .hist => False
  | .hist, .law => False
  | .law, .member _ => withLaw = true
  | .law, .hist => withLaw = true
  | .law, .law => False

/-- Membership in the three levels: member, history, law. -/
def historyConjunct : HistoryFact → HistoryFact → Prop
  | .member m, .member n => m = n
  | .hist, .member _ => False
  | .law, .member _ => False
  | .member _, .hist => True
  | .hist, .hist => True
  | .law, .hist => False
  | .member _, .law => True
  | .hist, .law => True
  | .law, .law => True

/-- Truth of a history fact at a world. -/
def historyHolds : HistoryWorld → HistoryFact → Prop
  | .lawful, .member _ => True
  | .lawful, .hist => True
  | .lawful, .law => True
  | .rogue, .member _ => True
  | .rogue, .hist => True
  | .rogue, .law => False
  | .cut k, .member n => n < k
  | .cut _, .hist => False
  | .cut _, .law => False

/-- `withLaw = false` is the negative control: an infinite history whose every
member has a necessitating independent reason and whose whole has none. With
`withLaw = true` it is the positive control of a globally constrained infinite
history: a law supplies a necessitating independent reason for the whole, and is
itself the contingent stopping point. -/
def history (withLaw : Bool) : Arena HistoryWorld Empty HistoryFact :=
  basic everywhere historyHolds
    (fun w r f => w = .lawful ∧ historyLink withLaw r f)
    historyConjunct

/-- `false` is a necessary fact and `true` a fact true at the two `some` worlds.
The fact has a reason at `some true` and none at `some false`. -/
def modalGap : Arena (Option Bool) Empty Bool :=
  basic everywhere
    (fun w f => f = false ∨ w ≠ none)
    (fun w r f => w = some true ∧ r = false ∧ f = true)
    (fun g f => g = f)

/-- Facts of `modalGapDiagonal`. -/
inductive DiagonalFact | necessary | fact | unexplained

/-- `modalGap` with the fact "the fact is true and has no reason" added and given
a reason at its world. Distribution fails, so the bridge cannot fire. -/
def modalGapDiagonal : Arena (Option Bool) Empty DiagonalFact :=
  basic everywhere
    (fun w f => match f with
      | .necessary => True
      | .fact => w ≠ none
      | .unexplained => w = some false)
    (fun w r f => r = .necessary ∧ match f with
      | .necessary => False
      | .fact => w = some true
      | .unexplained => w = some false)
    (fun g f => match g, f with
      | .fact, .unexplained => True
      | .necessary, .necessary => True
      | .necessary, .fact => False
      | .necessary, .unexplained => False
      | .fact, .necessary => False
      | .fact, .fact => True
      | .unexplained, .necessary => False
      | .unexplained, .fact => False
      | .unexplained, .unexplained => True)

/-- A non-reflexive frame: both worlds see only `true`. The contingent fact `true`
holds at `false` alone, so nothing accessible from `false` makes it true. -/
def nonReflexive : Arena Bool Empty Bool :=
  basic (fun _ v => v = true)
    (fun w f => f = false ∨ w = false)
    (fun w r f => w = false ∧ r = false ∧ f = true)
    (fun g f => g = f)

/-- The frame of `nonReflexive` with no reasons at all. The world `false` is not
accessible from itself, so necessity of the PSR does not reach it. -/
def nonReflexiveBare : Arena Bool Empty Bool :=
  basic (fun _ v => v = true)
    (fun w f => f = false ∨ w = false)
    (fun _ _ _ => False)
    (fun g f => g = f)

/-- Every fact is true at both worlds, and each world has its own reason: the
fact at world `w` named by `w` itself. So `□ ∃ r` holds with no `∃ r □`. -/
def shiftingReason : Arena Bool Empty Bool :=
  basic everywhere (fun _ _ => True) (fun w r _ => r = w) (fun g f => g = f)

/-- Facts of the existence-only control. -/
inductive ExistOnlyFact | being | event

/-- Every existent has a reason, while a contingent nonexistential event has none. -/
def existenceOnly : Arena Bool Unit ExistOnlyFact where
  ontic := {
    frame := ⟨everywhere⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False }
  holds := fun w f => match f with
    | .being => True
    | .event => w = false
  exist := fun _ => .being
  explains := fun _ r f => match r, f with
    | .being, .being => True
    | .being, .event => False
    | .event, .being => False
    | .event, .event => False
  conjunct := fun g f => match g, f with
    | .being, .being => True
    | .being, .event => False
    | .event, .being => False
    | .event, .event => True

/-- Every contingent existent has a distinct existing cause in an infinite chain,
and no fact has a reason. Causal coverage does not supply explanation. -/
def causeOnly : Arena Bool Nat Nat where
  ontic := {
    frame := ⟨everywhere⟩
    ExistsAt := fun w _ => w = false
    Causes := fun _ y x => y = x + 1 }
  holds := fun w _ => w = false
  exist := id
  explains := fun _ _ _ => False
  conjunct := fun g f => g = f

/-- Single-world extensional domain: facts are propositions. Contingency is
absent, so this witnesses satisfiability of the extensional background only. -/
def extensionalTrivial : Arena Unit Empty Prop :=
  basic everywhere (fun _ p => p) (fun _ r f => r ∧ f) (fun g f => f → g)

/-- Two-world extensional domain: a reason is a fact true at both worlds, and it
reasons for every truth. Contingency, a totality and unrestricted coverage coexist
because reasons do not necessitate. -/
def extensionalGround : Arena Bool Empty (Bool → Prop) :=
  basic everywhere (fun w f => f w) (fun w r f => (∀ v, r v) ∧ f w)
    (fun g f => ∀ v, f v → g v)

/-- A reason for every truth by copying it. Worlds, accessibility and truth are
those of `A`. -/
def copy (A : Arena W B F) : Arena W B F :=
  { A with explains := fun w r f => r = f ∧ A.holds w f }

/-- #312's models as arenas. Facts are #312's existence facts together with its
reason tokens; a reason token is counted true at every world, because #312 gives
tokens no truth conditions of their own. Only existence facts are ever explained. -/
def ofModel {E : Type} (m : ExistencePSR.Model W E) :
    Arena W E (ExistencePSR.ExistenceFact E ⊕ ExistencePSR.Reason E) where
  ontic := m.ontic
  holds := fun w f => match f with
    | .inl (.fact x) => m.ontic.ExistsAt w x
    | .inr _ => True
  exist := fun x => .inl (.fact x)
  explains := fun w r f => match r, f with
    | .inr r, .inl f => m.explains w r f
    | .inl _, .inl _ => False
    | .inl _, .inr _ => False
    | .inr _, .inr _ => False
  conjunct := fun g f => g = f

/-! ## Certificates -/

/-- The seven-member incompatible core and the deletion witness for each member.

First conjunct: under the conjunct law, no arena has a world with a contingent
truth, an aggregate of all contingent truths, no brute contingent truth, factive
necessitating reasons, distribution, and contingent irreflexivity. Second
conjunct: `ReasonIndependent` can replace distribution and irreflexivity.
Remaining conjuncts each keep the conjunct law and every other member and refute
the deleted one, which certifies inclusion-minimality of the first bundle (not
minimum cardinality, and nothing about the second bundle). -/
def CollapseCore : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t c : F),
    ConjunctSound A → Factive A → Necessitating A → Distribution A →
    IrreflexiveContingent A → BCCFAt A a t → Contingent A a c → NoBrute A a → False) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t c : F),
    ConjunctSound A → Factive A → Necessitating A → ReasonIndependent A →
    BCCFAt A a t → Contingent A a c → NoBrute A a → False) ∧
  -- delete coverage: the brute terminus
  (ConjunctSound bruteTerminus ∧ Factive bruteTerminus ∧ Necessitating bruteTerminus ∧
    Distribution bruteTerminus ∧ IrreflexiveContingent bruteTerminus ∧
    BCCFAt bruteTerminus false .whole ∧ Contingent bruteTerminus false .whole ∧
    ¬ NoBrute bruteTerminus false) ∧
  -- delete factivity: a reason that is never true
  (ConjunctSound falseToken ∧ ¬ Factive falseToken ∧ Necessitating falseToken ∧
    Distribution falseToken ∧ IrreflexiveContingent falseToken ∧
    BCCFAt falseToken false true ∧ Contingent falseToken false true ∧
    NoBrute falseToken false) ∧
  -- delete necessitation: the necessary nonnecessitating ground
  (ConjunctSound (ground true) ∧ Factive (ground true) ∧ ¬ Necessitating (ground true) ∧
    Distribution (ground true) ∧ IrreflexiveContingent (ground true) ∧
    BCCFAt (ground true) false .choice ∧ Contingent (ground true) false .choice ∧
    NoBrute (ground true) false) ∧
  -- delete the aggregate: the cofinite domain, with every other member at every world
  (ConjunctSound cofinite ∧ Factive cofinite ∧ Necessitating cofinite ∧
    Distribution cofinite ∧ IrreflexiveContingent cofinite ∧
    (∀ a t, ¬ BCCFAt cofinite a t) ∧ (∀ a, ∃ c, Contingent cofinite a c) ∧
    (∀ a, NoBrute cofinite a)) ∧
  -- delete distribution: mutual reasons
  (ConjunctSound mutualReasons ∧ Factive mutualReasons ∧ Necessitating mutualReasons ∧
    ¬ Distribution mutualReasons ∧ IrreflexiveContingent mutualReasons ∧
    BCCFAt mutualReasons false true ∧ Contingent mutualReasons false true ∧ NoBrute mutualReasons false) ∧
  -- delete irreflexivity: a contingent fact that is its own reason
  (ConjunctSound selfWhole ∧ Factive selfWhole ∧ Necessitating selfWhole ∧
    Distribution selfWhole ∧ ¬ IrreflexiveContingent selfWhole ∧
    BCCFAt selfWhole false () ∧ Contingent selfWhole false () ∧
    NoBrute selfWhole false) ∧
  -- delete contingency: necessary impersonal ground, with no contingent fact
  (ConjunctSound allNecessary ∧ Factive allNecessary ∧ Necessitating allNecessary ∧
    Distribution allNecessary ∧ IrreflexiveContingent allNecessary ∧
    BCCFAt allNecessary false false ∧ (∀ w c, ¬ Contingent allNecessary w c) ∧
    NoBrute allNecessary false)

/-- Scope, plurality, modal and quality edges. Each clause names the extra
hypothesis that a valid edge uses, or a model that separates an invalid one.

* Scope: `FactPSR` gives both narrower PSRs; existence and contingent-fact PSR are
  incomparable.
* Plurality: on one infinite-history signature, member coverage does not give a
  reason for the whole, and a reason for the whole does not give contingent-fact PSR.
* Modality: necessity gives actuality and actuality gives weak PSR with reflexivity,
  and each fails in a non-reflexive frame; neither converse holds. World-relative
  reasons at every world do not give one stable reason. Weak PSR gives `NoBrute` under distribution
  and the diagonal facts, and each of those two bridges is needed. Extensional
  domains with entailment conjuncts supply the bridges, so weak PSR with factive,
  necessitating, distributing, irreflexive reasons then excludes contingency at the
  world, whereas a named such domain without necessitation (`extensionalGround`) has it.
* Causation: external causation and existence coverage are independent.
* Quality: copying gives `FactPSR`, necessitation and factivity over any truth
  assignment while independence fails wherever contingency exists. `FactPSR` yields
  `ContingentPSR` and `NoBrute` by the scope edges; `ExistencePSR` also needs `Coherent`,
  and weak PSR also needs reflexivity, so copying alone guarantees neither.
* Reuse: #312's `ExistencePSR` and `ContingentPSR` are the all-world forms of this
  arena's scopes restricted to existence facts, along `ofModel`. -/
def StrengthMap : Prop :=
  -- scope edges
  (∀ (W B F : Type) (A : Arena W B F) (w : W), FactPSR A w → ContingentPSR A w) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W),
    Coherent A → FactPSR A w → ExistencePSR A w) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W), ContingentPSR A w → NoBrute A w) ∧
  (Factive (ground false) ∧ Coherent (ground false) ∧ (∀ w, ContingentPSR (ground false) w) ∧
    Contingent (ground false) false .choice ∧ ¬ ExistencePSR (ground false) false) ∧
  (Factive existenceOnly ∧ Coherent existenceOnly ∧ (∀ w, ExistencePSR existenceOnly w) ∧
    Contingent existenceOnly false .event ∧ ¬ ContingentPSR existenceOnly false) ∧
  -- plurality edges, with every quality clause retained
  (∀ b, ConjunctSound (history b) ∧ Factive (history b) ∧ Necessitating (history b) ∧
    ReasonIndependent (history b) ∧ Distribution (history b) ∧
    IrreflexiveContingent (history b) ∧
    BCCFAt (history b) .lawful .law ∧
    Contingent (history b) .lawful .hist ∧ Contingent (history b) .lawful .law ∧
    (∀ n, Explained (history b) .lawful (.member n)) ∧
    ¬ Explained (history b) .lawful .law ∧
    ¬ CommonReason (history b) .lawful) ∧
  ¬ Explained (history false) .lawful .hist ∧
  Explained (history true) .lawful .hist ∧
  CommonReason (ground true) false ∧
  -- modal edges
  (∀ (W B F : Type) (A : Arena W B F) (w : W),
    (∀ v, Access A v v) → NecessaryPSR A w → ContingentPSR A w) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W),
    (∀ v, Access A v v) → ContingentPSR A w → WeakPSR A w) ∧
  (Factive nonReflexive ∧ ContingentPSR nonReflexive false ∧
    Contingent nonReflexive false true ∧ ¬ WeakPSR nonReflexive false) ∧
  (NecessaryPSR nonReflexiveBare false ∧ Contingent nonReflexiveBare false true ∧
    ¬ ContingentPSR nonReflexiveBare false) ∧
  (∀ (W B F : Type) (A : Arena W B F) (f : F),
    StableReason A f → ∀ w, A.holds w f → Explained A w f) ∧
  (Factive shiftingReason ∧ (∀ w, FactPSR shiftingReason w) ∧
    ∀ f, ¬ StableReason shiftingReason f) ∧
  (Factive modalGap ∧ Distribution modalGap ∧
    ContingentPSR modalGap (some true) ∧ ¬ NecessaryPSR modalGap (some true) ∧
    WeakPSR modalGap (some false) ∧ ¬ NoBrute modalGap (some false) ∧
    ¬ UnexplainedFacts modalGap (some false)) ∧
  (Factive modalGapDiagonal ∧ UnexplainedFacts modalGapDiagonal (some false) ∧
    ¬ Distribution modalGapDiagonal ∧
    WeakPSR modalGapDiagonal (some false) ∧ ¬ NoBrute modalGapDiagonal (some false)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W),
    Distribution A → UnexplainedFacts A a → WeakPSR A a → NoBrute A a) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W),
    Extensional A → EntailmentConjunct A → UnexplainedFacts A a ∧ ∃ t, BCCFAt A a t) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W),
    Extensional A → EntailmentConjunct A → Factive A → Necessitating A → Distribution A →
    IrreflexiveContingent A → WeakPSR A a → ∀ c, ¬ Contingent A a c) ∧
  (Extensional extensionalTrivial ∧ EntailmentConjunct extensionalTrivial ∧
    Factive extensionalTrivial ∧ Necessitating extensionalTrivial ∧
    Distribution extensionalTrivial ∧ IrreflexiveContingent extensionalTrivial ∧
    WeakPSR extensionalTrivial ()) ∧
  (Extensional extensionalGround ∧ EntailmentConjunct extensionalGround ∧
    Factive extensionalGround ∧ ¬ Necessitating extensionalGround ∧
    Distribution extensionalGround ∧ IrreflexiveContingent extensionalGround ∧
    FactPSR extensionalGround false ∧
    (∃ c, Contingent extensionalGround false c) ∧ (∃ t, BCCFAt extensionalGround false t)) ∧
  -- the cofinite domain: strong scope and quality at every world, finite closure
  ((∀ a, FactPSR cofinite a) ∧ ReasonIndependent cofinite ∧
    (∀ l r, ∃ j, cofinite.conjunct l j ∧ cofinite.conjunct r j ∧
      ∀ v, cofinite.holds v j ↔ (cofinite.holds v l ∧ cofinite.holds v r))) ∧
  -- causal edges
  (LocalCausalPrinciple causeOnly.ontic ∧ ExternalCause causeOnly false ∧
    Coherent causeOnly ∧ Factive causeOnly ∧ Contingent causeOnly false 0 ∧
    ¬ ExistencePSR causeOnly false ∧ ¬ ContingentPSR causeOnly false) ∧
  (ExistencePSR (ground true) false ∧ ¬ ExternalCause (ground true) false ∧
    LocalCausalPrinciple (ground true).ontic) ∧
  -- quality edges: the target copy against an independent root
  (∀ (W B F : Type) (A : Arena W B F),
    (copy A).ontic = A.ontic ∧ (copy A).holds = A.holds ∧
    (∀ w, FactPSR (copy A) w) ∧ Necessitating (copy A) ∧ Factive (copy A)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (c : F),
    Contingent A w c → ¬ ReasonIndependent (copy A) ∧ ¬ IrreflexiveContingent (copy A)) ∧
  ReasonIndependent (ground true) ∧ ¬ Necessitating (ground true) ∧
  -- reuse of #312 along the embedding
  (∀ (W E : Type) (m : TruthCore.Explanation.ExistencePSR.Model W E),
    Coherent (ofModel m) ∧
    (TruthCore.Explanation.ExistencePSR.ExistencePSR m ↔ ∀ w, ExistencePSR (ofModel m) w) ∧
    (TruthCore.Explanation.ExistencePSR.ContingentPSR m ↔
      ∀ w x, Contingent (ofModel m) w ((ofModel m).exist x) →
        Explained (ofModel m) w ((ofModel m).exist x)))

end TruthCore.Explanation.PSRStrength
