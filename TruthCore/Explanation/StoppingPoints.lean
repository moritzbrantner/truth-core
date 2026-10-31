import TruthCore.Explanation.PSRSelfApplication

/-!
# Applying one standard to every explanatory stopping point (#746)

Each test below is stated over the #755 arena and takes an arena, a world and a fact.
None mentions God, nature, law or whole. The same tests are then evaluated on a brute
contingent terminus, a necessary ground, a contingent law, an unexplained infinite
whole, a necessitating necessary stop and a domain with no stopping point.

The tests are analyst-stated. Nothing here says that any of them is the right demand
on an explanation, and every model is an analyst-built structure that shows a formal
bundle satisfiable, not metaphysically possible. `explains` remains the uninterpreted
parameter of #755. The arena has no predicate for personal agency, so these tests
cannot separate a necessary personal ground from a necessary impersonal one.
See `docs/notes/stopping-points-746.md` for the interpretation and the limits.
-/
namespace TruthCore.Explanation.StoppingPoints

open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.PSRSelfApplication

variable {W B F : Type}

/-! ## The tests -/

/-- `s` is a true fact with no reason at `w` other than, possibly, itself. A
self-reason does not stop a fact being terminal: that is the case at issue. -/
def Terminal (A : Arena W B F) (w : W) (s : F) : Prop :=
  A.holds w s ∧ ∀ r, A.explains w r s → r = s

/-- Everything `s` is a reason for at `w` is true at each accessible world where `s` is.
This is the #755 necessitation clause, restricted to the reasons `s` gives. -/
def WorkNecessitates (A : Arena W B F) (w : W) (s : F) : Prop :=
  ∀ t, A.explains w s t → ∀ v, Access A w v → A.holds v s → A.holds v t

/-- Nothing `s` is a reason for at `w` agrees with `s` at every accessible world. Unlike
`ReasonIndependent`, which binds contingent targets only, this binds every target. -/
def WorkIndependent (A : Arena W B F) (w : W) (s : F) : Prop :=
  ∀ t, A.explains w s t → ¬ ∀ v, Access A w v → (A.holds v s ↔ A.holds v t)

/-- True at every accessible world. -/
def NecessaryFact (A : Arena W B F) (w : W) (f : F) : Prop :=
  ∀ v, Access A w v → A.holds v f

/-! ## Foundations and the candidate norm -/

/-- `Supplied A w S f`: `f` is in `S`, or has a reason at `w` that is supplied from `S`.
One reason is enough at each step: reasons are alternatives, not joint requirements. -/
inductive Supplied (A : Arena W B F) (w : W) (S : F → Prop) : F → Prop
  | base {f : F} : S f → Supplied A w S f
  | step {r f : F} : A.explains w r f → Supplied A w S r → Supplied A w S f

/-- Some reason for `t` at `w` is supplied from `s` alone. So `s` does explanatory work
toward `t` through at least one reason, and an isolated fact supplies nothing. -/
def Strict (A : Arena W B F) (w : W) (s t : F) : Prop :=
  ∃ r, A.explains w r t ∧ Supplied A w (· = s) r

/-- `s` is a terminal fact with a reason for `t` supplied from it, and `t` is not supplied
from any other terminal fact (`t` itself counts, if terminal and distinct from `s`).
"Indispensable" means no more than this. In particular, a second terminal fact that also
supplies `t` removes the status from both. -/
def Foundation (A : Arena W B F) (w : W) (s t : F) : Prop :=
  Terminal A w s ∧ Strict A w s t ∧
    ¬ Supplied A w (fun x => Terminal A w x ∧ x ≠ s) t

/-- The candidate norm, restricted to contingent stops: no foundation at `w` is a
contingent truth with no reason. An OPEN norm: nothing here asserts it. -/
def NoBruteFoundation (A : Arena W B F) (w : W) : Prop :=
  ∀ s t, Foundation A w s t → ¬ BruteAt A w s

/-- The same norm with the contingency restriction removed: every foundation at `w` has
some reason there, possibly itself. An OPEN norm: nothing here asserts it. -/
def NoUnreasonedFoundation (A : Arena W B F) (w : W) : Prop :=
  ∀ s t, Foundation A w s t → Explained A w s

/-- Any two terminal facts from which `t` is supplied are the same fact. -/
def SingleStop (A : Arena W B F) (w : W) (t : F) : Prop :=
  ∀ x y, Terminal A w x → Terminal A w y →
    Supplied A w (· = x) t → Supplied A w (· = y) t → x = y

/-! ## Models -/

/-- Two contingent roots, each a reason for the same effect, with no reason for either.
Both are brute and neither is a foundation of the effect. -/
inductive TwinFact | left | right | effect

/-- See `TwinFact`. All three facts are true at world `false` alone. -/
def twinRoots : Arena Bool Empty TwinFact :=
  basic everywhere (fun w _ => w = false)
    (fun w r f => match r, f with
      | .left, .effect => w = false
      | .right, .effect => w = false
      | .left, .left => False
      | .left, .right => False
      | .right, .left => False
      | .right, .right => False
      | .effect, .left => False
      | .effect, .right => False
      | .effect, .effect => False)
    (fun g f => g = f)

/-- `false` is an unexplained necessary fact that necessitates the necessary `true`. No
fact is contingent. -/
def necessaryStop : Arena Bool Empty Bool :=
  basic everywhere (fun _ _ => True) (fun _ r f => r = false ∧ f = true) (fun g f => g = f)

/-- One contingent fact with no reason and no work. -/
def isolated : Arena Bool Empty Unit :=
  basic everywhere (fun w _ => w = false) (fun _ _ _ => False) (fun g f => g = f)

/-- No fact is true, and nothing is a reason for anything. -/
def noTruth : Arena Unit Empty Unit :=
  basic everywhere (fun _ _ => False) (fun _ _ _ => False) (fun g f => g = f)

/-- `false` is a contingent fact that is its own reason and a reason for `true`. -/
def selfWork : Arena Bool Empty Bool :=
  basic everywhere (fun w _ => w = false) (fun w r _ => w = false ∧ r = false)
    (fun g f => g = f)

/-- Facts of `rivalStops`. -/
inductive RivalFact | nature | brute | effect

/-- A necessary terminal fact and a contingent terminal fact in one arena, where the
contingent one is a reason for the effect, so that one stance can be compared on both. -/
def rivalStops : Arena Bool Empty RivalFact :=
  basic everywhere
    (fun w f => match f with
      | .nature => True
      | .brute => w = false
      | .effect => w = false)
    (fun w r f => match r, f with
      | .brute, .effect => w = false
      | .brute, .brute => False
      | .brute, .nature => False
      | .nature, .effect => False
      | .nature, .brute => False
      | .nature, .nature => False
      | .effect, .effect => False
      | .effect, .brute => False
      | .effect, .nature => False)
    (fun g f => g = f)

/-- Demands reasons for the contingent stop and not for the necessary one. Accepts all. -/
def modalExemption : Stance RivalFact :=
  ⟨fun _ => True, fun _ => False, fun f => f = .brute⟩

/-! ## Certificates -/

/-- **One standard, every stopping point.**

* Two inconsistent cores, with a deletion witness for each member. A contingent truth,
  no brute contingent truth there, factive and necessitating reasons, and well-founded
  reasons at that world cannot stand together. Unrestricted fact coverage, factive
  reasons, well-founded reasons and a truth cannot stand together, and this second core
  has no necessitation clause and no exemption for necessary facts. Each core forces
  rejecting at least one member and does not say which.
* Work transfers contingency: under factivity, a fact whose work necessitates, and that
  is a reason for a contingent truth, is itself contingent. So a terminal such fact under
  contingent irreflexivity is brute.
* The three-way fork for a terminal fact that is a reason for a contingent truth, under
  factivity and given two decisions: brute, or a contingent self-reason, or a noncontingent
  stop whose work does not necessitate. The three exclude each other, and each has a
  named witness.
* The table: the same readings evaluated at each named stop. The stop with no work has
  no work readings, and the stop-free domain has no terminal fact.
* Whole-level reuse of #755: under the conjunct law, an aggregate of all contingent
  truths, a contingent truth, factive, necessitating and independent reasons cannot stand
  with no brute contingent truth. Under the conjunct law and necessitating, independent
  reasons, a conjunct is no reason for a contingent aggregate. The domain with no stop
  has no aggregate.
* A necessary fact with uniformly independent work is no reason for a necessary fact,
  itself included. `ground true` and `copy (ground false)` both have the ground as its own
  reason, and the ground is true at every world in each; `ground false` does not.
* One stance is selective on `Terminal` and restricted on `Contingent`, on one pair of
  facts. -/
def StoppingMap : Prop :=
  -- first core
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (c : F),
    Contingent A a c → NoBrute A a → Factive A → Necessitating A →
    WellFounded (A.explains a) → False) ∧
  (¬ NoBrute bruteTerminus false ∧ Contingent bruteTerminus false .effect ∧
    Factive bruteTerminus ∧ Necessitating bruteTerminus ∧
    WellFounded (bruteTerminus.explains false)) ∧
  ((∀ w c, ¬ Contingent necessaryStop w c) ∧ NoBrute necessaryStop false ∧
    Factive necessaryStop ∧ Necessitating necessaryStop ∧
    WellFounded (necessaryStop.explains false)) ∧
  (¬ Factive falseToken ∧ Contingent falseToken false true ∧ NoBrute falseToken false ∧
    Necessitating falseToken ∧ WellFounded (falseToken.explains false)) ∧
  (¬ Necessitating (ground false) ∧ Contingent (ground false) false .choice ∧
    NoBrute (ground false) false ∧ Factive (ground false) ∧
    WellFounded ((ground false).explains false)) ∧
  (∀ a, ¬ WellFounded (cofinite.explains a) ∧ (∃ c, Contingent cofinite a c) ∧
    NoBrute cofinite a ∧ Factive cofinite ∧ Necessitating cofinite) ∧
  (¬ WellFounded (mutualReasons.explains false) ∧ Contingent mutualReasons false true ∧
    NoBrute mutualReasons false ∧ Factive mutualReasons ∧ Necessitating mutualReasons) ∧
  -- second core
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t : F),
    A.holds a t → FactPSR A a → Factive A → WellFounded (A.explains a) → False) ∧
  (¬ FactPSR (ground false) false ∧ (ground false).holds false .ground ∧
    Factive (ground false) ∧ WellFounded ((ground false).explains false)) ∧
  (¬ WellFounded ((ground true).explains false) ∧ (ground true).holds false .ground ∧
    FactPSR (ground true) false ∧ Factive (ground true)) ∧
  (¬ Factive falseToken ∧ falseToken.holds false true ∧ FactPSR falseToken false ∧
    WellFounded (falseToken.explains false)) ∧
  ((∀ t, ¬ noTruth.holds () t) ∧ FactPSR noTruth () ∧ Factive noTruth ∧
    WellFounded (noTruth.explains ())) ∧
  -- work transfers contingency
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (s t : F),
    Factive A → A.explains w s t → Contingent A w t → WorkNecessitates A w s →
      Contingent A w s) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (s t : F),
    Factive A → IrreflexiveContingent A → Terminal A w s → A.explains w s t →
      Contingent A w t → WorkNecessitates A w s → BruteAt A w s) ∧
  -- the fork
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (s t : F),
    Factive A → Terminal A w s → A.explains w s t → Contingent A w t →
    (Contingent A w s ∨ ¬ Contingent A w s) → (Explained A w s ∨ ¬ Explained A w s) →
      BruteAt A w s ∨ (Contingent A w s ∧ A.explains w s s) ∨
        (¬ Contingent A w s ∧ ¬ WorkNecessitates A w s)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (s : F),
    ¬ (BruteAt A w s ∧ (Contingent A w s ∧ A.explains w s s)) ∧
    ¬ (BruteAt A w s ∧ (¬ Contingent A w s ∧ ¬ WorkNecessitates A w s)) ∧
    ¬ ((Contingent A w s ∧ A.explains w s s) ∧
      (¬ Contingent A w s ∧ ¬ WorkNecessitates A w s))) ∧
  (BruteAt bruteTerminus false .terminus ∧ Terminal bruteTerminus false .terminus ∧
    bruteTerminus.explains false .terminus .effect ∧ Contingent bruteTerminus false .effect) ∧
  (Contingent selfWork false false ∧ selfWork.explains false false false ∧
    Terminal selfWork false false ∧ selfWork.explains false false true ∧
    Contingent selfWork false true ∧ Factive selfWork) ∧
  (¬ Contingent (ground true) false .ground ∧ ¬ WorkNecessitates (ground true) false .ground ∧
    Terminal (ground true) false .ground ∧ (ground true).explains false .ground .choice ∧
    Contingent (ground true) false .choice) ∧
  -- the table: terminal, has a reason, contingent, work necessitates, work independent
  (Terminal bruteTerminus false .terminus ∧ ¬ Explained bruteTerminus false .terminus ∧
    Contingent bruteTerminus false .terminus ∧ WorkNecessitates bruteTerminus false .terminus ∧
    ¬ WorkIndependent bruteTerminus false .terminus) ∧
  (Terminal (ground true) false .ground ∧ Explained (ground true) false .ground ∧
    ¬ Contingent (ground true) false .ground ∧ ¬ WorkNecessitates (ground true) false .ground ∧
    ¬ WorkIndependent (ground true) false .ground) ∧
  (Terminal (ground false) false .ground ∧ ¬ Explained (ground false) false .ground ∧
    ¬ Contingent (ground false) false .ground ∧ ¬ WorkNecessitates (ground false) false .ground ∧
    WorkIndependent (ground false) false .ground) ∧
  (Terminal (history true) .lawful .law ∧ ¬ Explained (history true) .lawful .law ∧
    Contingent (history true) .lawful .law ∧ WorkNecessitates (history true) .lawful .law ∧
    WorkIndependent (history true) .lawful .law) ∧
  (Terminal (history false) .lawful .hist ∧ ¬ Explained (history false) .lawful .hist ∧
    Contingent (history false) .lawful .hist ∧
    (∀ t, ¬ (history false).explains .lawful .hist t)) ∧
  (Terminal necessaryStop false false ∧ ¬ Explained necessaryStop false false ∧
    ¬ Contingent necessaryStop false false ∧ WorkNecessitates necessaryStop false false ∧
    ¬ WorkIndependent necessaryStop false false) ∧
  (Terminal allNecessary false false ∧ Explained allNecessary false false ∧
    ¬ Contingent allNecessary false false ∧ WorkNecessitates allNecessary false false ∧
    ¬ WorkIndependent allNecessary false false) ∧
  (∀ a s, ¬ Terminal cofinite a s) ∧
  -- wholes
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t c : F),
    ConjunctSound A → Factive A → Necessitating A → ReasonIndependent A →
    BCCFAt A a t → Contingent A a c → NoBrute A a → False) ∧
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (r t : F),
    ConjunctSound A → Necessitating A → ReasonIndependent A →
    A.conjunct r t → A.explains a r t → Contingent A a t → False) ∧
  (∀ a t, ¬ BCCFAt cofinite a t) ∧
  -- uniform independence and the self-reason
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (r f : F),
    WorkIndependent A w r → NecessaryFact A w r → NecessaryFact A w f →
      ¬ A.explains w r f) ∧
  ((ground true).explains false .ground .ground ∧
    (copy (ground false)).explains false .ground .ground ∧
    (∀ v, (copy (ground false)).holds v .ground ↔ (ground true).holds v .ground) ∧
    ¬ (ground false).explains false .ground .ground) ∧
  -- the exemption's standing depends on the feature
  (Selective modalExemption (Terminal rivalStops false) .brute .nature ∧
    Restricted modalExemption (Contingent rivalStops false) .brute .nature)

/-- **Testing a no-brute-indispensable-foundation norm.**

* The implication: a contingent explained truth with a single stop, under factive,
  necessitating and well-founded reasons, cannot stand with `NoBruteFoundation`. Each of
  the seven members is deleted by a named model.
* Survivors: `NoBruteFoundation` is satisfied by a necessary ground, with or without a
  self-reason, by a domain with no stop, by two brute roots, and by one isolated brute
  fact. So it does not exclude brute truths: it holds in named models that have them.
* `NoUnreasonedFoundation` drops the restriction. It fails at the necessary ground
  without a self-reason and holds with one. It also holds in every target-copy arena,
  where every reason only copies its target.
* The norm's verdict on an arena and the support of a named fact vary independently: named
  arenas and inquiries give each of the four combinations.
* Counting reasons: given factivity, `copy A` has a reason for everything that has one
  in `A`, and keeps truth and the ontic structure. For `bruteTerminus` it also gains a
  reason for the terminus and loses reason independence. So there a preference for more
  facts explained, with nothing else, favours the copy. -/
def FoundationNormTest : Prop :=
  -- the implication
  (∀ (W B F : Type) (A : Arena W B F) (a : W) (t : F),
    Contingent A a t → Explained A a t → SingleStop A a t → Factive A → Necessitating A →
    WellFounded (A.explains a) → NoBruteFoundation A a → False) ∧
  -- deletions, in the order of the hypotheses
  ((∀ w c, ¬ Contingent necessaryStop w c) ∧ Explained necessaryStop false true ∧
    SingleStop necessaryStop false true ∧ Factive necessaryStop ∧
    Necessitating necessaryStop ∧ WellFounded (necessaryStop.explains false) ∧
    NoBruteFoundation necessaryStop false) ∧
  (Contingent isolated false () ∧ ¬ Explained isolated false () ∧
    SingleStop isolated false () ∧ Factive isolated ∧ Necessitating isolated ∧
    WellFounded (isolated.explains false) ∧ NoBruteFoundation isolated false) ∧
  (Contingent twinRoots false .effect ∧ Explained twinRoots false .effect ∧
    ¬ SingleStop twinRoots false .effect ∧ Factive twinRoots ∧ Necessitating twinRoots ∧
    WellFounded (twinRoots.explains false) ∧ NoBruteFoundation twinRoots false) ∧
  (Contingent falseToken false true ∧ Explained falseToken false true ∧
    SingleStop falseToken false true ∧ ¬ Factive falseToken ∧ Necessitating falseToken ∧
    WellFounded (falseToken.explains false) ∧ NoBruteFoundation falseToken false) ∧
  (Contingent (ground false) false .choice ∧ Explained (ground false) false .choice ∧
    SingleStop (ground false) false .choice ∧ Factive (ground false) ∧
    ¬ Necessitating (ground false) ∧ WellFounded ((ground false).explains false) ∧
    NoBruteFoundation (ground false) false) ∧
  (∀ a, ∃ c, Contingent cofinite a c ∧ Explained cofinite a c ∧ SingleStop cofinite a c ∧
    Factive cofinite ∧ Necessitating cofinite ∧ ¬ WellFounded (cofinite.explains a) ∧
    NoBruteFoundation cofinite a) ∧
  (Contingent bruteTerminus false .effect ∧ Explained bruteTerminus false .effect ∧
    SingleStop bruteTerminus false .effect ∧ Factive bruteTerminus ∧
    Necessitating bruteTerminus ∧ WellFounded (bruteTerminus.explains false) ∧
    ¬ NoBruteFoundation bruteTerminus false ∧
    Foundation bruteTerminus false .terminus .effect ∧ BruteAt bruteTerminus false .terminus) ∧
  -- the contingent law is a brute foundation of the whole
  (Foundation (history true) .lawful .law .hist ∧ BruteAt (history true) .lawful .law ∧
    ¬ NoBruteFoundation (history true) .lawful) ∧
  -- survivors that keep a brute truth
  (NoBruteFoundation twinRoots false ∧ BruteAt twinRoots false .left ∧
    BruteAt twinRoots false .right ∧
    twinRoots.explains false .left .effect ∧ twinRoots.explains false .right .effect) ∧
  (NoBruteFoundation isolated false ∧ BruteAt isolated false ()) ∧
  -- the necessary ground under both norms
  (NoBruteFoundation (ground true) false ∧ NoUnreasonedFoundation (ground true) false ∧
    NoBruteFoundation (ground false) false ∧ ¬ NoUnreasonedFoundation (ground false) false ∧
    Foundation (ground false) false .ground .choice) ∧
  -- the target copy passes the unrestricted norm
  (∀ (W B F : Type) (A : Arena W B F) (w : W), NoUnreasonedFoundation (copy A) w) ∧
  -- the norm and support vary independently
  (¬ NoBruteFoundation (scene true) .a ∧ Supported science .a .root ∧
    BruteAt (scene true) .a .root ∧ Foundation (scene true) .a .root .event ∧
    ¬ Supported blank .a .root ∧
    NoBruteFoundation (ground false) false ∧ Supported groundInquiry false .choice ∧
    ¬ Supported (⟨fun _ _ _ => False⟩ : Inquiry Bool GroundFact) false .choice) ∧
  -- counting reasons
  (∀ (W B F : Type) (A : Arena W B F), Factive A →
    (copy A).holds = A.holds ∧ (copy A).ontic = A.ontic ∧
    ∀ w f, Explained A w f → Explained (copy A) w f) ∧
  (¬ Explained bruteTerminus false .terminus ∧
    Explained (copy bruteTerminus) false .terminus ∧
    ¬ ReasonIndependent (copy bruteTerminus))

end TruthCore.Explanation.StoppingPoints
