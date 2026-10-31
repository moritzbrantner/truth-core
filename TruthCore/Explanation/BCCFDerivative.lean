import TruthCore.Explanation.PSRStrength

/-!
# Testing the reply that derivative facts differ from direct facts (#365)

`CollapseCore` (#755) has single-fact reasons. A reply that lets an aggregate be
explained by its conjuncts together needs plural reasons, because no one conjunct
necessitates the aggregate. This module adds exactly that relation and a stipulated
class `D` of direct facts over the same `Arena`. `ofSingle` embeds single reasons.

`G w Xs f` reads: at world `w`, the facts `Xs` together are admitted as a reason why
`f` obtains. It is an interpreted parameter, not assumed causal, transitive,
asymmetric, well-founded, contrastive or necessitating; each such condition is a
separately named hypothesis. `D` is a parameter too: nothing here says which facts
are direct. See `docs/notes/bccf-sources-365.md` for the interpretation and for the
sourced readings. Models show that encoded bundles are satisfiable, not that they
are metaphysically possible. No PSR and no reply is established here.
-/
namespace TruthCore.Explanation.BCCFDerivative

open TruthCore.Explanation.PSRStrength

variable {W B F : Type}

/-- Plural reasons at a world. -/
abbrev Plural (W F : Type) := W → (F → Prop) → F → Prop

/-- Some facts are together admitted as a reason for `f` at `w`. -/
def Covered (G : Plural W F) (w : W) (f : F) : Prop := ∃ Xs, G w Xs f

/-- Every contingent truth at `a` in the class `D` has a plural reason. -/
def CoveredOn (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop) : Prop :=
  ∀ f, D f → Contingent A a f → Covered G a f

/-- All the reasons and the explanandum are true at the world of the explanation. -/
def PFactive (A : Arena W B F) (G : Plural W F) : Prop :=
  ∀ w Xs f, G w Xs f → (∀ x, Xs x → A.holds w x) ∧ A.holds w f

/-- The reasons jointly suffice modally for what they explain. -/
def PNecessitating (A : Arena W B F) (G : Plural W F) : Prop :=
  ∀ w Xs f, G w Xs f → ∀ v, Access A w v → (∀ x, Xs x → A.holds v x) → A.holds v f

/-- At every accessible world where the explanandum fails, some reason fails. This is
one contrastive reading: the reasons discriminate the fact from every such world. -/
def PContrast (A : Arena W B F) (G : Plural W F) : Prop :=
  ∀ w Xs f, G w Xs f → ∀ v, Access A w v → ¬ A.holds v f → ∃ x, Xs x ∧ ¬ A.holds v x

/-- Reasons for an aggregate are reasons for each of its conjuncts, everywhere. -/
def PDistribution (A : Arena W B F) (G : Plural W F) : Prop :=
  ∀ w Xs f g, G w Xs f → A.conjunct g f → G w Xs g

/-- Reasons for the fact `t` at `a` are reasons for each conjunct of `t` there. -/
def DistributesAt (A : Arena W B F) (G : Plural W F) (a : W) (t : F) : Prop :=
  ∀ Xs g, G a Xs t → A.conjunct g t → G a Xs g

/-- No contingent fact is among the reasons for itself. -/
def PartIrreflexive (A : Arena W B F) (G : Plural W F) : Prop :=
  ∀ w Xs e, Contingent A w e → G w Xs e → ¬ Xs e

/-- Every fact is true or not true at every world. The general theorems that pass
from "not all reasons hold" to a failing reason use this instead of a logical axiom.
The last conjunct of `DerivativeReply` shows that every model below meets it, so no
model here deletes it. -/
def Bivalent (A : Arena W B F) : Prop :=
  ∀ v f, A.holds v f ∨ ¬ A.holds v f

/-- `t` is true at `a` and has every contingent truth of `D` at `a` as a conjunct.
`t` itself need not be in `D`. -/
def DirectAggregate (A : Arena W B F) (a : W) (D : F → Prop) (t : F) : Prop :=
  A.holds a t ∧ ∀ q, D q → Contingent A a q → A.conjunct q t

/-- A contingent reason for a fact in `D` is in `D`: nothing outside the class is
among the contingent reasons of a fact inside it. This is the condition that makes
`D` a class of facts not explained by derivative ones. -/
def ClosedUnderReasons (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop) : Prop :=
  ∀ f Xs x, D f → G a Xs f → Xs x → Contingent A a x → D x

/-- `e` is a contingent reason among the reasons of the contingent fact `f` at `a`. -/
def Below (A : Arena W B F) (G : Plural W F) (a : W) (e f : F) : Prop :=
  Contingent A a e ∧ Contingent A a f ∧ ∃ Xs, G a Xs f ∧ Xs e

/-- No infinite descent and no circle among contingent reasons at `a`. -/
def WellFoundedReasons (A : Arena W B F) (G : Plural W F) (a : W) : Prop :=
  WellFounded (Below A G a)

/-- A single reason as a plural reason with exactly one member. -/
def ofSingle (A : Arena W B F) : Plural W F :=
  fun w Xs f => ∃ r, A.explains w r f ∧ ∀ x, Xs x ↔ x = r

/-! ## Models

All use universal accessibility. `.a` and `.b` are members and `.whole` their
aggregate; each model's actual world is named in the certificate. -/

/-- Members and aggregate. -/
inductive PairFact | a | b | whole

/-- Three coextensive facts true only at world `false`. Every fact is a conjunct of
`whole` and of itself. -/
def pair : Arena Bool Empty PairFact :=
  basic everywhere (fun w _ => w = false) (fun _ _ _ => False)
    (fun g f => f = .whole ∨ g = f)

/-- The aggregate has its two members as reasons; the members have no reason. -/
def bruteMembers : Plural Bool PairFact :=
  fun w Xs f => w = false ∧ f = .whole ∧ ∀ x, Xs x ↔ (x = .a ∨ x = .b)

/-- As `bruteMembers`, and each member has the other as its reason. -/
def loopMembers : Plural Bool PairFact :=
  fun w Xs f => bruteMembers w Xs f ∨
    (w = false ∧ ((f = .a ∧ ∀ x, Xs x ↔ x = .b) ∨ (f = .b ∧ ∀ x, Xs x ↔ x = .a)))

/-- Each member has the other as its reason; the aggregate has no reason. -/
def scopeOnly : Plural Bool PairFact :=
  fun w Xs f => w = false ∧ ((f = .a ∧ ∀ x, Xs x ↔ x = .b) ∨ (f = .b ∧ ∀ x, Xs x ↔ x = .a))

/-- As `pair`, but `.b` is not a conjunct of `whole`: only `.a` and `.whole` are. -/
def pairOutside : Arena Bool Empty PairFact :=
  basic everywhere (fun w _ => w = false) (fun _ _ _ => False)
    (fun g f => (g = .a ∧ f = .whole) ∨ g = f)

/-- `.b` is the sole reason of `.a` and of `.whole`, and has no reason. -/
def outsideReason : Plural Bool PairFact :=
  fun w Xs f => w = false ∧ (f = .a ∨ f = .whole) ∧ ∀ x, Xs x ↔ x = .b

/-- As `pair`, but `.b` is true nowhere. -/
def pairToken : Arena Bool Empty PairFact :=
  basic everywhere (fun w f => w = false ∧ f ≠ .b) (fun _ _ _ => False)
    (fun g f => (g = .a ∧ f = .whole) ∨ g = f)

/-- As `pair`, but every fact is true everywhere. -/
def pairNecessary : Arena Bool Empty PairFact :=
  basic everywhere (fun _ _ => True) (fun _ _ _ => False) (fun g f => f = .whole ∨ g = f)

/-- No reasons at all. -/
def noReasons : Plural Bool PairFact := fun _ _ _ => False

/-- An endless descending chain with no circle. `some n` is the `n`-th member and
`none` the aggregate. World `none` contains all members and the aggregate; world
`some k` contains only the members below `k`. -/
def chain : Arena (Option Nat) Empty (Option Nat) :=
  basic everywhere
    (fun w f => match f, w with
      | none, w => w = none
      | some _, none => True
      | some n, some k => n < k)
    (fun _ _ _ => False)
    (fun g f => f = none ∨ g = f)

/-- Each member has the next as its reason; the aggregate has all members. -/
def chainReasons : Plural (Option Nat) (Option Nat) :=
  fun w Xs f => w = none ∧
    ((∃ n, f = some n ∧ ∀ x, Xs x ↔ x = some (n + 1)) ∨
      (f = none ∧ ∀ x, Xs x ↔ ∃ n, x = some n))

/-! ## Certificate -/

/-- The direct-versus-derivative test.

1. The aggregate argument with plural reasons is valid.
2. It stays valid when `t` aggregates only the class `D`, with no assumption that `t`
   is in `D`: calling the totality derivative does not by itself block it.
3. Without any aggregate or distribution: on a class closed under contingent reasons,
   coverage, factive necessitating reasons and well-foundedness exclude contingency.
4. The same with `PContrast` in place of necessitation and bivalence.
5. `PContrast` with bivalence gives necessitation.
6. Single reasons embed in plural reasons.

The remaining conjuncts are models. None shows metaphysical possibility. -/
def DerivativeReply : Prop :=
  -- 1. the plural aggregate argument
  (∀ (W B F : Type) (A : Arena W B F) (G : Plural W F) (a : W) (t c : F),
    ConjunctSound A → PFactive A G → PNecessitating A G → PDistribution A G →
    PartIrreflexive A G → Bivalent A → BCCFAt A a t → Contingent A a c →
    CoveredOn A G a (fun _ => True) → False) ∧
  -- 2. a totality of the direct facts, not assumed direct
  (∀ (W B F : Type) (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop) (t c : F),
    ConjunctSound A → PFactive A G → PNecessitating A G → DistributesAt A G a t →
    PartIrreflexive A G → Bivalent A → ClosedUnderReasons A G a D →
    DirectAggregate A a D t → D c → Contingent A a c → Covered G a t → False) ∧
  -- 3. no aggregate, no distribution
  (∀ (W B F : Type) (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop),
    PFactive A G → PNecessitating A G → Bivalent A → WellFoundedReasons A G a →
    ClosedUnderReasons A G a D → CoveredOn A G a D →
    ∀ f, D f → ¬ Contingent A a f) ∧
  -- 4. the contrastive variant
  (∀ (W B F : Type) (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop),
    PFactive A G → PContrast A G → WellFoundedReasons A G a →
    ClosedUnderReasons A G a D → CoveredOn A G a D →
    ∀ f, D f → ¬ Contingent A a f) ∧
  -- 5. contrast and necessitation
  (∀ (W B F : Type) (A : Arena W B F) (G : Plural W F),
    Bivalent A → PContrast A G → PNecessitating A G) ∧
  -- 6. the embedding of single reasons
  (∀ (W B F : Type) (A : Arena W B F),
    (Factive A → PFactive A (ofSingle A)) ∧
    (Necessitating A → PNecessitating A (ofSingle A)) ∧
    (Distribution A → PDistribution A (ofSingle A)) ∧
    (IrreflexiveContingent A → PartIrreflexive A (ofSingle A)) ∧
    (∀ w f, Explained A w f ↔ Covered (ofSingle A) w f)) ∧
  -- the aggregate has its conjuncts as reasons and the members have none
  (ConjunctSound pair ∧ PFactive pair bruteMembers ∧ PNecessitating pair bruteMembers ∧
    PartIrreflexive pair bruteMembers ∧ WellFoundedReasons pair bruteMembers false ∧
    ClosedUnderReasons pair bruteMembers false (· ≠ .whole) ∧
    BCCFAt pair false .whole ∧ Contingent pair false .a ∧
    Covered bruteMembers false .whole ∧ ¬ Covered bruteMembers false .a ∧
    ¬ DistributesAt pair bruteMembers false .whole ∧
    CoveredOn pair bruteMembers false (· = .whole) ∧
    ¬ CoveredOn pair bruteMembers false (· ≠ .whole)) ∧
  -- full coverage with a circle among the members
  (ConjunctSound pair ∧ PFactive pair loopMembers ∧ PNecessitating pair loopMembers ∧
    PartIrreflexive pair loopMembers ∧ BCCFAt pair false .whole ∧ Contingent pair false .a ∧
    ClosedUnderReasons pair loopMembers false (fun _ => True) ∧
    CoveredOn pair loopMembers false (fun _ => True) ∧
    ¬ DistributesAt pair loopMembers false .whole ∧
    ¬ WellFoundedReasons pair loopMembers false) ∧
  -- full coverage with an endless chain among the members
  (ConjunctSound chain ∧ PFactive chain chainReasons ∧ PNecessitating chain chainReasons ∧
    PartIrreflexive chain chainReasons ∧ BCCFAt chain none none ∧ Contingent chain none (some 0) ∧
    ClosedUnderReasons chain chainReasons none (fun _ => True) ∧
    CoveredOn chain chainReasons none (fun _ => True) ∧
    ¬ DistributesAt chain chainReasons none none ∧
    ¬ WellFoundedReasons chain chainReasons none ∧
    (∀ e, ¬ Below chain chainReasons none e e)) ∧
  -- a necessary reason that does not necessitate, keeping everything else
  ((∀ v, (ground true).holds v .ground) ∧
    ConjunctSound (ground true) ∧ PFactive (ground true) (ofSingle (ground true)) ∧
    PDistribution (ground true) (ofSingle (ground true)) ∧
    PartIrreflexive (ground true) (ofSingle (ground true)) ∧
    WellFoundedReasons (ground true) (ofSingle (ground true)) false ∧
    BCCFAt (ground true) false .choice ∧ Contingent (ground true) false .choice ∧
    ClosedUnderReasons (ground true) (ofSingle (ground true)) false (fun _ => True) ∧
    CoveredOn (ground true) (ofSingle (ground true)) false (fun _ => True) ∧
    ¬ PNecessitating (ground true) (ofSingle (ground true)) ∧
    ¬ PContrast (ground true) (ofSingle (ground true))) ∧
  -- the scope reading: distribution kept, the aggregate has no reason
  (ConjunctSound pair ∧ PFactive pair scopeOnly ∧ PNecessitating pair scopeOnly ∧
    PDistribution pair scopeOnly ∧ PartIrreflexive pair scopeOnly ∧
    BCCFAt pair false .whole ∧ Contingent pair false .a ∧
    ClosedUnderReasons pair scopeOnly false (· ≠ .whole) ∧
    CoveredOn pair scopeOnly false (· ≠ .whole) ∧ ¬ Covered scopeOnly false .whole) ∧
  -- closure deleted: the direct fact has a contingent reason outside the class
  (ConjunctSound pairOutside ∧ PFactive pairOutside outsideReason ∧
    PNecessitating pairOutside outsideReason ∧
    DistributesAt pairOutside outsideReason false .whole ∧
    PartIrreflexive pairOutside outsideReason ∧
    WellFoundedReasons pairOutside outsideReason false ∧
    DirectAggregate pairOutside false (· = .a) .whole ∧ Contingent pairOutside false .a ∧
    CoveredOn pairOutside outsideReason false (· = .a) ∧
    Covered outsideReason false .whole ∧
    ¬ ClosedUnderReasons pairOutside outsideReason false (· = .a)) ∧
  -- factivity deleted: a reason that is true nowhere
  (ConjunctSound pairToken ∧ PNecessitating pairToken outsideReason ∧
    WellFoundedReasons pairToken outsideReason false ∧
    ClosedUnderReasons pairToken outsideReason false (· = .a) ∧
    Contingent pairToken false .a ∧ CoveredOn pairToken outsideReason false (· = .a) ∧
    ¬ PFactive pairToken outsideReason) ∧
  -- contingency deleted: every other member of conjunct 3 holds
  (PFactive pairNecessary noReasons ∧ PNecessitating pairNecessary noReasons ∧
    WellFoundedReasons pairNecessary noReasons false ∧
    ClosedUnderReasons pairNecessary noReasons false (fun _ => True) ∧
    CoveredOn pairNecessary noReasons false (fun _ => True) ∧
    ∀ f, ¬ Contingent pairNecessary false f) ∧
  -- every model is bivalent
  (Bivalent pair ∧ Bivalent chain ∧ Bivalent (ground true) ∧ Bivalent pairOutside ∧
    Bivalent pairToken ∧ Bivalent pairNecessary)

end TruthCore.Explanation.BCCFDerivative
