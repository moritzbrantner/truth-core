module

public import TruthCore.Causality.DeiFiliusLivingNineScope

/-! *Immensus* and *incomprehensibilis*: typed sibling readings of the last two
Dei Filius primitives

`DeiFiliusAttributeField` leaves five attributes as explicitly identified
primitives; `DeiFiliusLivingSelfOperation` and `DeiFiliusLordBlessed` give
living, lord and most blessed typed siblings. This module does the same for the
remaining two, so that every primitive of the Dei Filius endpoint has a typed
sibling and each passage to a primitive is one named open sense bridge.

**Immense.** IMMENSE_1 is the primitive `Primitives.Immense` (measured or
contained by no place and present to everything that is, after ST I q.8).
IMMENSE_2, `IsImmenseAsInfiniteCauseOfAll`, types the two grounds the Summa gives
that existing vocabulary can express: g is infinite (INFINITE_1, q.7 a.1:
unreceived subsistent being, limited by no receiver) and g causes the being of
everything else (`IsCreatorOfAll`). IMMENSE_2 types causing being, which q.8 a.3
gives as the GROUND of presence by essence; it does not type presence itself.
`CausesIn … esse` is tenseless and leaves open whether the causing originates or
sustains being (`DEF-CAUSE-OF-PERFECTION`). It is a typed proxy for Aquinas's
grounds, not a sense in which Dei Filius calls God immense. At a being with the
nine both conjuncts are contained in the nine: infinity is one of them, and the
creator conjunct is contained BY DEFINITION in supreme goodness (as in
`DeiFiliusLordBlessed`), so no bridge is needed and nothing is independently
derived. Not typed, and carried by the sense bridge: place and containment
("not contained by place", q.8 a.2, a.4); presence *by power* and *by presence*
(knowledge) of q.8 a.3; the q.8 a.1 contact principle (an agent is joined to
that on which it acts), which turns causing into being present; sustaining as
against merely originating causation (conservation, q.104 a.1), which makes the
presence present now; and immediacy of presence (`CausesIn` does not distinguish
mediate from immediate causing).

**Incomprehensible.** INCOMPREHENSIBLE_1 is the primitive
`Primitives.Incomprehensible` (no created intellect knows g as perfectly as g is
knowable, ST I q.12 a.7). INCOMPREHENSIBLE_2,
`IsIncomprehensibleToCausedIntellects`, types its quantifier structure and its
ground: g is infinite, and no intellect whose being is caused by another
(`IsCausedIntellect`) comprehends g. Comprehension needs one new relation, the
explicitly identified primitive `Comprehension.Comprehends` (x knows y as
perfectly as y is knowable, q.12 a.7); no existing relation of the corpus relates
a knower to a known being (the `Veracity.Knows` of `NamingVeracityBatch1` is
propositional). At a being with the nine INCOMPREHENSIBLE_2 follows from two new
open bridges: what is caused as to being by another is not INFINITE_1 (after
q.7 a.2) and a finite (non-INFINITE_1) intellect does not comprehend an
INFINITE_1 being (the q.12 a.7 mechanism). The derivation uses only the
infinity conjunct of the nine. Given infinity, these two bridges and the sense
bridge below jointly entail the old bridge `InfiniteIsIncomprehensible`, so the
new route splits the old commitment into finer premises; it is not a weaker total
commitment. INCOMPREHENSIBLE_2 is not unknowability, by the form of its
definition: it negates only `Comprehends`, and no knowing relation is typed.
Control part 1 shows only that self-comprehension is allowed.

The senses are not identified (invariant 7). Each passage from the typed sense
to the primitive is one explicit sense bridge
(`InfiniteCauseOfAllIsImmense`, `InfiniteUncomprehendedIsIncomprehensible`),
each strictly weaker than the old bridge it replaces in the new routes
(`CreatorOfAllIsImmense`, `InfiniteIsIncomprehensible`).

Analyst formulations, attribution deferred: the Summa articles motivate the
readings and bridges; no claim states any of them. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusImmenseIncomprehensible

open TruthCore.Case.Catholicism
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine)

/-! ## Immense -/

/-- IMMENSE_2, *immensus* read through its typed grounds: g is infinite
(INFINITE_1) and causes the being of every other being in act as to being
(tenselessly: originating or sustaining is left open). After ST I q.7 a.1 and
q.8 a.3, which gives causing being as the ground of presence *by essence*; presence
itself is not typed. A typed proxy for Aquinas's grounds, not a sense in which Dei
Filius calls God immense. Not typed: place and containment, presence by power and
by knowledge, the contact principle, sustaining causation, immediacy (see the
module docstring). -/
def IsImmenseAsInfiniteCauseOfAll {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (Infinite : Being → Prop)
    (g : Being) : Prop :=
  Infinite g ∧ IsCreatorOfAll InAct CausesIn esse g

/-- Whatever has the nine is IMMENSE_2. Derived with no premise
(`nineAreImmenseAsInfiniteCauseOfAll`): infinity is one of the nine, and the
creator conjunct is contained by definition in supreme goodness. -/
def NineAreImmenseAsInfiniteCauseOfAll {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g → IsImmenseAsInfiniteCauseOfAll InAct CausesIn esse Infinite g

/-- Open sense bridge IMMENSE_2 → IMMENSE_1: whatever is infinite and causes the
being of everything else is immense (measured or contained by no place and present
to everything that is). After q.8 a.1–3. It carries what IMMENSE_2 leaves untyped:
place and containment, presence by power and by knowledge, the q.8 a.1 contact
principle (an agent is joined to that on which it acts), sustaining as against
merely originating causation (q.104 a.1; contested by existential inertia, Schmid
2021), and immediacy. Its antecedent does not say that the being is incorporeal, so "contained by no
place" rests on infinity alone in this bridge. Strictly
weaker than `CreatorOfAllIsImmense` (its antecedent adds infinity;
`Control.Controls` part 2). -/
def InfiniteCauseOfAllIsImmense {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (Infinite : Being → Prop)
    (D : Primitives Being) : Prop :=
  ∀ g, IsImmenseAsInfiniteCauseOfAll InAct CausesIn esse Infinite g → D.Immense g

/-! ## Incomprehensible -/

/-- Explicitly identified PRIMITIVE relation (Encode first).

* `Comprehends x y` — x comprehends y: x knows y as perfectly as y is knowable
  (ST I q.12 a.7: *comprehendere* is to know a thing perfectly, as much as it is
  knowable). Distinguished from knowing y truly, or attaining y, which does not
  require comprehension (q.12 a.7 ad 1); a knower may know y without
  comprehending it. Open obligation: a typed measure of knowability (q.12 a.1: a
  thing is knowable insofar as it is in act) and of an intellect's power of
  knowing, from which comprehension could be defined.

No axiom constrains it; the bridge `FiniteIntellectDoesNotComprehendInfinite` is
the only constraint anything here places on it. -/
structure Comprehension (Being : Type) where
  Comprehends : Being → Being → Prop

/-- A caused intellect (the typed reading of "created intellect"): x has
intellect and some other being causes x's being. Weaker than created in the
Dei Filius sense: creation from nothing is not typed (as in `IsCreatorOfAll`). -/
def IsCausedIntellect {Being Respect : Type} (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (HasIntellect : Being → Prop) (x : Being) : Prop :=
  HasIntellect x ∧ ∃ c, c ≠ x ∧ CausesIn c x esse

/-- INCOMPREHENSIBLE_2, *incomprehensibilis* read after ST I q.12 a.7: g is
infinite (INFINITE_1), and no caused intellect comprehends g. Not unknowability,
by the form of this definition: it negates only `Comprehends`, and no knowing
relation is typed. The infinity conjunct records the q.12 a.7 ground; it also
makes the old bridge entail the new sense bridge (a convenience for the strength
order). -/
def IsIncomprehensibleToCausedIntellects {Being Respect : Type}
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Infinite HasIntellect : Being → Prop) (C : Comprehension Being) (g : Being) : Prop :=
  Infinite g ∧ ∀ x, IsCausedIntellect CausesIn esse HasIntellect x → ¬ C.Comprehends x g

/-- Open bridge: whatever has its being caused by another being is not
INFINITE_1. After ST I q.7 a.2 and its ad 1 (it is against the nature of a made
thing to be absolutely infinite): anything besides God has its being received
into a distinct receiving potency, and so limited.

SCOPE CONDITION (a domain stipulation binding every premise that shares this
`Being` and `CausesIn`): elements of `Being` are individuated by their act of
being, so things numerically one in esse are one element. The divine persons,
who share one numerically identical esse, are therefore not distinct elements and
cannot be represented as such; the Son's being from the Father is no instance of
`CausesIn c x esse` with `c ≠ x`, and its esse is not received into a distinct
receiving potency. (That q.33 a.1 ad 1 prefers "principle" to "cause" is only a
terminological aside: it notes that the Greeks say "cause".) -/
def CausedIsNotInfinite {Being Respect : Type} (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (Infinite : Being → Prop) : Prop :=
  ∀ x, (∃ c, c ≠ x ∧ CausesIn c x esse) → ¬ Infinite x

/-- Open bridge: no intellect that is not INFINITE_1 comprehends a being that is
INFINITE_1. After ST I q.12 a.7: God is infinitely knowable, being infinite act,
and no created intellect knows him infinitely, since its power of knowing (even
raised by the light of glory) is finite. The bridge reads "finite intellect" as an
intellect whose being is not INFINITE_1, so it also carries the step from finite
being to finite power of knowing. -/
def FiniteIntellectDoesNotComprehendInfinite {Being : Type} (Infinite HasIntellect : Being → Prop)
    (C : Comprehension Being) : Prop :=
  ∀ g x, Infinite g → HasIntellect x → ¬ Infinite x → ¬ C.Comprehends x g

/-- Whatever has the nine is INCOMPREHENSIBLE_2. Derived
(`nineAreIncomprehensibleToCausedIntellects`) from the two bridges above. -/
def NineAreIncomprehensibleToCausedIntellects {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (C : Comprehension Being) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g →
    IsIncomprehensibleToCausedIntellects CausesIn esse Infinite HasIntellect C g

/-- Open sense bridge INCOMPREHENSIBLE_2 → INCOMPREHENSIBLE_1: whatever is
infinite and comprehended by no caused intellect is incomprehensible (known by no
created intellect as perfectly as it is knowable). It carries what
INCOMPREHENSIBLE_2 leaves untyped: that the primitive `Comprehends` is knowing as
perfectly as knowable, and that "created" (from nothing) intellects are among the
caused ones. Strictly weaker than `InfiniteIsIncomprehensible` (its antecedent
adds that no caused intellect comprehends g; `Control.Controls` part 3). -/
def InfiniteUncomprehendedIsIncomprehensible {Being Respect : Type}
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Infinite HasIntellect : Being → Prop) (C : Comprehension Being) (D : Primitives Being) :
    Prop :=
  ∀ g, IsIncomprehensibleToCausedIntellects CausesIn esse Infinite HasIntellect C g →
    D.Incomprehensible g

/-! ## Controls -/

namespace Control

open TruthCore.Causality.DeiFiliusLivingNineScope.Control (inAct noPotency isTrue yes no)

/-- Primitives whose immensity and incomprehensibility are `i` and `c`, the rest
false. -/
def prims (i c : Bool → Prop) : Primitives Bool :=
  ⟨fun _ => False, fun _ => False, i, c, fun _ => False⟩

/-- Only `true` causes anything. -/
def causesFromTrue (c _ : Bool) (_ : Unit) : Prop := c = true

/-- `true` comprehends everything; `false` comprehends nothing. -/
def trueComprehends : Comprehension Bool := ⟨fun x _ => x = true⟩

/-- Everything comprehends everything. -/
def allComprehend : Comprehension Bool := ⟨fun _ _ => True⟩

/-- The nine on two beings (`Bool`) with one respect, in which everything is in
act and good, nothing in potency or composite; `true` alone causes, is GOD_4 and
is infinite; both have intellect and will. -/
abbrev Nine (Infinite : Bool → Prop) (g : Bool) : Prop :=
  HasTheNine inAct inAct noPotency causesFromTrue () isTrue no Infinite yes yes yes g

/-- Checked interpretations on two beings (`Bool`; `true` alone causes and is
GOD_4; both have intellect and will; one respect, in which everything is in act;
nothing is in potency):

1. nonvacuity: with `true` alone infinite and comprehending everything (itself
   included), both bridges hold, and `true` has the nine, IMMENSE_2 and
   INCOMPREHENSIBLE_2 while comprehending itself (so INCOMPREHENSIBLE_2 allows
   self-comprehension; that it is not unknowability follows from the definition's
   form, not from this model);
2. strictness for immense: nothing is infinite or IMMENSE_1. The new sense bridge
   holds and `CreatorOfAllIsImmense` fails (a cause of the being of all that is
   not infinite is not immense);
3. strictness for incomprehensible: `true` alone infinite, everything
   comprehends everything, nothing INCOMPREHENSIBLE_1. The new sense bridge holds
   and `InfiniteIsIncomprehensible` fails;
4. the finite-intellect bridge is needed: everything comprehends everything,
   `true` alone infinite; the caused-is-not-infinite bridge holds, `true` has the
   nine and is not INCOMPREHENSIBLE_2;
5. the caused-is-not-infinite bridge is needed: both beings infinite, everything
   comprehends everything; the finite-intellect bridge holds (vacuously: nothing
   is finite), `true` has the nine and is not INCOMPREHENSIBLE_2;
6. sense-mixing control: with nothing IMMENSE_1 or INCOMPREHENSIBLE_1, `true` has
   the nine and is IMMENSE_2 and INCOMPREHENSIBLE_2 without being IMMENSE_1 or
   INCOMPREHENSIBLE_1. -/
def Controls : Prop :=
  (CausedIsNotInfinite causesFromTrue () isTrue ∧
    FiniteIntellectDoesNotComprehendInfinite isTrue yes trueComprehends ∧
    Nine isTrue true ∧ IsImmenseAsInfiniteCauseOfAll inAct causesFromTrue () isTrue true ∧
    IsIncomprehensibleToCausedIntellects causesFromTrue () isTrue yes trueComprehends true ∧
    trueComprehends.Comprehends true true) ∧
  (InfiniteCauseOfAllIsImmense inAct causesFromTrue () no (prims no no) ∧
    ¬ CreatorOfAllIsImmense inAct causesFromTrue () (prims no no)) ∧
  (InfiniteUncomprehendedIsIncomprehensible causesFromTrue () isTrue yes allComprehend
      (prims no no) ∧
    ¬ InfiniteIsIncomprehensible isTrue (prims no no)) ∧
  (CausedIsNotInfinite causesFromTrue () isTrue ∧ Nine isTrue true ∧
    ¬ IsIncomprehensibleToCausedIntellects causesFromTrue () isTrue yes allComprehend true) ∧
  (FiniteIntellectDoesNotComprehendInfinite yes yes allComprehend ∧ Nine yes true ∧
    ¬ IsIncomprehensibleToCausedIntellects causesFromTrue () yes yes allComprehend true) ∧
  (Nine isTrue true ∧ IsImmenseAsInfiniteCauseOfAll inAct causesFromTrue () isTrue true ∧
    IsIncomprehensibleToCausedIntellects causesFromTrue () isTrue yes trueComprehends true ∧
    ¬ (prims no no).Immense true ∧ ¬ (prims no no).Incomprehensible true)

end Control
end TruthCore.Causality.DeiFiliusImmenseIncomprehensible
