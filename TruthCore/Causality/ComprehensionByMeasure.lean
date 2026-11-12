module

public import Mathlib.Order.Max
public import TruthCore.Causality.DeiFiliusImmenseIncomprehensible

/-! Comprehension by measure: a typed account of *comprehendere* (ST I q.12 a.7)
from a degree of act, a degree of knowability and a degree of knowing

`DeiFiliusImmenseIncomprehensible` introduced the explicitly identified primitive
`Comprehension.Comprehends` (COMPREHEND_1, definition `4afe4ab4`: x knows y as
perfectly as y is knowable) and constrained it only by the open bridge
`FiniteIntellectDoesNotComprehendInfinite` (`bbac932e`, after q.12 a.7). Its
review judged that bridge not near-definitional: it carries "infinite act →
infinitely knowable" and "finite being → finite power of knowing" unstated.
This module types both steps, so the bridge is derived and could have failed.

**Vocabulary.** A degree scale `Deg` with a Mathlib `Preorder` and three
explicitly identified primitive measures (`Measures`): a being's degree of act
(`actDegree`), its degree of knowability (`knowability`, how far it is knowable
in itself) and a three-place degree of knowing (`KnowsAt x y d`: x knows y with a
knowing whose perfection is d). "Maximal" in the names below means GREATEST:
Mathlib's `IsTop` (every degree on the scale is at most it), not `IsMax`
(nothing strictly exceeds it), which is weaker on a non-total `Preorder`.
Defined from them:

* COMPREHEND_2, `ComprehendsByMeasure M x y`: x knows y at some degree that
  reaches y's knowability (q.12 a.7: to comprehend is to know a thing as
  perfectly as it is knowable);
* `PowerOfKnowingBoundedBy M x p`: every knowing of x is at most p (p bounds
  x's power of knowing).

**Premises** (all open, analyst formulations, attribution deferred):

* `InfiniteActIsMaximal`: whatever is INFINITE_1 has the greatest degree of act
  (q.7 a.1: unreceived subsistent being is limited by nothing);
* `KnowableInsofarAsInAct`: everything is knowable at least to the degree it is
  in act (q.12 a.1; q.16 a.3, pinned claim `191c4ad9`: *unumquodque inquantum
  habet de esse, intantum est cognoscibile*);
* `NonInfiniteActIsNotMaximal`: whatever is not INFINITE_1 does not have a
  maximal degree of act (q.7 a.2: what has received being is limited);
* `KnowingWithinKnowersAct`: nothing knows anything at a degree beyond its own
  degree of act (q.12 a.4 and a.7: knowing follows the mode of the knower, and
  the created light of glory is finite).

**Derivations.** The first two give `InfiniteIsMaximallyKnowable`; the last two
give `NonInfiniteIntellectHasNonMaximalPower`; those two give COMPREHEND_2's
version of the bridge by transitivity of `≤` (if x COMPREHEND_2s g, then
`knowability g ≤ d ≤ p`, so a non-maximal p would be maximal). The old bridge
about COMPREHEND_1 then follows with one sense bridge,
`Comprehend1IsComprehend2` (whatever COMPREHEND_1s y COMPREHEND_2s y).

**Senses.** COMPREHEND_1 (the primitive) and COMPREHEND_2 (defined here) are not
identified (invariant 7, disambiguation COMPREHEND). The only passage between
them is the open sense bridge, which carries the comparison between knowing and
knowability for COMPREHEND_1 pairs, and requires every COMPREHEND_1 to show up as
some `KnowsAt` degree. The converse is not assumed (controls).

**Commensurability.** The one shared scale is a commitment spread over four
premises, not only the sense bridge: `KnowableInsofarAsInAct` (act ≤
knowability), `KnowingWithinKnowersAct` (knowing ≤ the knower's act),
`InfiniteActIsMaximal` through `IsTop` (every degree of anything, act,
knowability or knowing, is at most the INFINITE_1's act, and so comparable with
it) and the sense bridge (knowability ≤ knowing for COMPREHEND_1 pairs). It is
the main open warrant gap of this account. The `Preorder` leaves other degrees
incomparable where no premise forces a comparison.

**Scale commitment.** `InfiniteActIsMaximal` presupposes that the scale has a
greatest degree wherever something is INFINITE_1: on any scale with no maximum (Mathlib
`NoMaxOrder`, such as ℕ) it entails that nothing is INFINITE_1 (control part 8).
That is a fact about the premise's form, not an objection to it; whether degrees
of act are cardinal-like sizes is the question an objection would have to argue.
-/

@[expose] public section

namespace TruthCore.Causality.ComprehensionByMeasure

open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
  (Comprehension FiniteIntellectDoesNotComprehendInfinite)

/-- Explicitly identified PRIMITIVE measures (Encode first), on a degree scale
`Deg` (a Mathlib `Preorder`: reflexive and transitive, not assumed total or
antisymmetric).

* `actDegree x` — the degree to which x is in act (in being). Ordinary meaning:
  a living thing is more in act than a stone, a knower more than a plant (the
  grades of q.4 a.2 and the *quarta via*). It is not the Fourth Way comparative
  `MoreIn esse`, which relates beings rather than assigning degrees; no bridge
  between them is stated.
* `knowability y` — the degree to which y is knowable in itself (not to us):
  q.12 a.1, a thing is knowable insofar as it is in act. Distinguished from
  being known by anyone: a degree of knowability may exceed every degree at
  which y is actually known.
* `KnowsAt x y d` — x knows y with a knowing whose perfection is d. Example: a
  mathematician knows a theorem by demonstration at a higher degree than one who
  holds it on authority (the example of q.12 a.7). Several degrees for one pair
  are allowed; knowing nothing is allowed.

No axiom constrains them; the premises below are the only constraints. -/
structure Measures (Being Deg : Type) where
  actDegree : Being → Deg
  knowability : Being → Deg
  KnowsAt : Being → Being → Deg → Prop

variable {Being Deg : Type} [Preorder Deg]

/-- COMPREHEND_2: x knows y at some degree that reaches y's degree of
knowability (ST I q.12 a.7: *comprehendere* is to know a thing perfectly, as
much as it is knowable). Defined, not primitive. It is not knowing y (which
needs only some `KnowsAt x y d`), and it does not require knowing y beyond its
knowability. -/
def ComprehendsByMeasure (M : Measures Being Deg) (x y : Being) : Prop :=
  ∃ d, M.KnowsAt x y d ∧ M.knowability y ≤ d

/-- `p` bounds x's power of knowing: x knows nothing at a degree above `p`.
Stated over x's actual knowings (no modality), so it is the weakest form of a
bound on a power that the derivation needs. -/
def PowerOfKnowingBoundedBy (M : Measures Being Deg) (x : Being) (p : Deg) : Prop :=
  ∀ y d, M.KnowsAt x y d → d ≤ p

/-- OPEN premise: whatever is INFINITE_1 has the greatest degree of act (Mathlib
`IsTop`: every degree on the scale is at most it; stronger than `IsMax`, nothing
strictly exceeds it, on a non-total `Preorder`). After ST I q.7 a.1: esse not
received in anything is limited by nothing. Consequence of `IsTop` on the one
shared scale: every degree of act, knowability and knowing of every being is
comparable with, and at most, the INFINITE_1's act. Presupposes a scale with a
greatest degree wherever something is INFINITE_1 (control part 8). -/
def InfiniteActIsMaximal (Infinite : Being → Prop) (M : Measures Being Deg) : Prop :=
  ∀ g, Infinite g → IsTop (M.actDegree g)

/-- OPEN premise: everything is knowable at least to the degree it is in act.
After ST I q.12 a.1 and q.16 a.3 (pinned claim `191c4ad9`: a thing is knowable
insofar as it has being); only the direction "at least" is used. -/
def KnowableInsofarAsInAct (M : Measures Being Deg) : Prop :=
  ∀ y, M.actDegree y ≤ M.knowability y

/-- Derived (`infiniteIsMaximallyKnowable`): whatever is INFINITE_1 is maximally
knowable. The q.12 a.7 premise "God is infinitely knowable". -/
def InfiniteIsMaximallyKnowable (Infinite : Being → Prop) (M : Measures Being Deg) : Prop :=
  ∀ g, Infinite g → IsTop (M.knowability g)

/-- OPEN premise: whatever is not INFINITE_1 does not have the greatest degree of
act (`¬ IsTop`). After ST I q.7 a.2: what has received being is limited. Weakest
form: it is met as soon as some degree is not at most the being's act, even an
incomparable one; the `IsMax` sibling (`¬ IsMax`: something strictly exceeds it)
would be stronger and closer to "limited", and is not registered. -/
def NonInfiniteActIsNotMaximal (Infinite : Being → Prop) (M : Measures Being Deg) : Prop :=
  ∀ x, ¬ Infinite x → ¬ IsTop (M.actDegree x)

/-- OPEN premise: nothing knows anything at a degree above its own degree of
act; a knower's degree of act bounds its power of knowing. After ST I q.12 a.4
(knowledge is according to the mode of the knower) and a.7 (the created light of
glory, by which the blessed see God, is finite). The degree of act is meant as
the knower's whole act, including an added perfection such as that light; the
measures have no state index, so a knower before and after receiving the light
is represented by reading the measures for one state at a time. -/
def KnowingWithinKnowersAct (M : Measures Being Deg) : Prop :=
  ∀ x, PowerOfKnowingBoundedBy M x (M.actDegree x)

/-- Derived (`nonInfiniteIntellectHasNonMaximalPower`): every intellect that is
not INFINITE_1 has a power of knowing bounded by a non-maximal degree. The q.12
a.7 premise "a created intellect knows finitely", in its weakest form: the bound
need only be non-maximal, not finite in any quantitative sense. -/
def NonInfiniteIntellectHasNonMaximalPower (Infinite HasIntellect : Being → Prop)
    (M : Measures Being Deg) : Prop :=
  ∀ x, HasIntellect x → ¬ Infinite x → ∃ p, ¬ IsTop p ∧ PowerOfKnowingBoundedBy M x p

/-- Derived (`finiteIntellectDoesNotComprehend2Infinite`): no intellect that is
not INFINITE_1 COMPREHEND_2s an INFINITE_1 being. The COMPREHEND_2 sibling of
`FiniteIntellectDoesNotComprehendInfinite`. -/
def FiniteIntellectDoesNotComprehend2Infinite (Infinite HasIntellect : Being → Prop)
    (M : Measures Being Deg) : Prop :=
  ∀ g x, Infinite g → HasIntellect x → ¬ Infinite x → ¬ ComprehendsByMeasure M x g

/-- OPEN sense bridge COMPREHEND_1 → COMPREHEND_2: whatever stands in the
primitive comprehension relation to y knows y at a degree reaching y's
knowability. It carries that the primitive's gloss "as perfectly as y is
knowable" is measured on the same scale as the degrees of knowing and of
knowability, so that they are comparable. The converse is not assumed. -/
def Comprehend1IsComprehend2 (C : Comprehension Being) (M : Measures Being Deg) : Prop :=
  ∀ x y, C.Comprehends x y → ComprehendsByMeasure M x y

/-! ## Controls -/

namespace Control

/-- `true` alone is INFINITE_1. -/
def inf (b : Bool) : Prop := b = true

/-- Both beings have intellect. -/
def yes (_ : Bool) : Prop := True

/-- Degrees of act and knowability equal to the being itself (`true` maximal),
and each being knows everything at its own degree of act. -/
def exact : Measures Bool Bool := ⟨id, id, fun x _ d => d = x⟩

/-- Everything at the lowest degree. -/
def flat : Measures Bool Bool := ⟨fun _ => false, fun _ => false, fun _ _ d => d = false⟩

/-- Act as in `exact`, knowability flat. -/
def lowKnowability : Measures Bool Bool := ⟨id, fun _ => false, fun x _ d => d = x⟩

/-- Everything at the highest degree. -/
def high : Measures Bool Bool := ⟨fun _ => true, fun _ => true, fun _ _ d => d = true⟩

/-- Act and knowability as in `exact`, everyone knows at the highest degree. -/
def overreach : Measures Bool Bool := ⟨id, id, fun _ _ d => d = true⟩

/-- Checked interpretations on two beings (`Bool`; `true` alone INFINITE_1; both
have intellect) with the degree scale `Bool` (`false < true`):

1. nonvacuity (`exact`, primitive comprehension = COMPREHEND_2): all four
   premises and the sense bridge hold, the bridge `bbac932e` holds, `true`
   comprehends itself in both senses, and `false` COMPREHEND_2s itself (a
   finite intellect comprehends a finite being);
2. without `InfiniteActIsMaximal` (`flat`): the other three premises hold,
   maximal knowability fails, the power premise holds, and `false` COMPREHEND_2s
   `true`;
3. without `KnowableInsofarAsInAct` (`lowKnowability`): the other three hold and
   `false` COMPREHEND_2s `true`;
4. without `NonInfiniteActIsNotMaximal` (`high`): the other three hold, maximal
   knowability holds, the power premise fails, and `false` COMPREHEND_2s `true`;
5. without `KnowingWithinKnowersAct` (`overreach`): the other three hold and
   `false` COMPREHEND_2s `true`;
6. the sense bridge is needed: with `exact` and everything comprehending
   everything in the primitive sense, the COMPREHEND_2 bridge holds, the sense
   bridge fails and `bbac932e` fails;
7. the senses are not identified: with `exact` and nothing comprehending
   anything in the primitive sense, the sense bridge holds and its converse
   fails;
8. scale commitment: on any scale with no maximum, `InfiniteActIsMaximal`
   entails that nothing is INFINITE_1.

A finite countermodel shows a premise is needed in that interpretation, not that
it is false. -/
def Controls : Prop :=
  (InfiniteActIsMaximal inf exact ∧ KnowableInsofarAsInAct exact ∧
    NonInfiniteActIsNotMaximal inf exact ∧ KnowingWithinKnowersAct exact ∧
    Comprehend1IsComprehend2 ⟨ComprehendsByMeasure exact⟩ exact ∧
    FiniteIntellectDoesNotComprehendInfinite inf yes ⟨ComprehendsByMeasure exact⟩ ∧
    ComprehendsByMeasure exact true true ∧ ComprehendsByMeasure exact false false) ∧
  (¬ InfiniteActIsMaximal inf flat ∧ KnowableInsofarAsInAct flat ∧
    NonInfiniteActIsNotMaximal inf flat ∧ KnowingWithinKnowersAct flat ∧
    ¬ InfiniteIsMaximallyKnowable inf flat ∧
    NonInfiniteIntellectHasNonMaximalPower inf yes flat ∧
    ComprehendsByMeasure flat false true) ∧
  (InfiniteActIsMaximal inf lowKnowability ∧ ¬ KnowableInsofarAsInAct lowKnowability ∧
    NonInfiniteActIsNotMaximal inf lowKnowability ∧ KnowingWithinKnowersAct lowKnowability ∧
    ComprehendsByMeasure lowKnowability false true) ∧
  (InfiniteActIsMaximal inf high ∧ KnowableInsofarAsInAct high ∧
    ¬ NonInfiniteActIsNotMaximal inf high ∧ KnowingWithinKnowersAct high ∧
    InfiniteIsMaximallyKnowable inf high ∧
    ¬ NonInfiniteIntellectHasNonMaximalPower inf yes high ∧
    ComprehendsByMeasure high false true) ∧
  (InfiniteActIsMaximal inf overreach ∧ KnowableInsofarAsInAct overreach ∧
    NonInfiniteActIsNotMaximal inf overreach ∧ ¬ KnowingWithinKnowersAct overreach ∧
    ComprehendsByMeasure overreach false true) ∧
  (FiniteIntellectDoesNotComprehend2Infinite inf yes exact ∧
    ¬ Comprehend1IsComprehend2 ⟨fun _ _ => True⟩ exact ∧
    ¬ FiniteIntellectDoesNotComprehendInfinite inf yes ⟨fun _ _ => True⟩) ∧
  (Comprehend1IsComprehend2 ⟨fun _ _ => False⟩ exact ∧
    ¬ ∀ x y, ComprehendsByMeasure exact x y → (⟨fun _ _ => False⟩ : Comprehension Bool).Comprehends x y) ∧
  (∀ (B D : Type) [Preorder D] [NoMaxOrder D] (Infinite : B → Prop) (M : Measures B D),
    InfiniteActIsMaximal Infinite M → ∀ g, ¬ Infinite g)

end Control
end TruthCore.Causality.ComprehensionByMeasure
