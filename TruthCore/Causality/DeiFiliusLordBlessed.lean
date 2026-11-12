module

public import TruthCore.Causality.DeiFiliusLivingNineScope
public import TruthCore.Causality.DeiFiliusOperationFromIntellect
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question103.Government

/-! *Dominus* and *beatissimus*: typed sibling readings of two Dei Filius primitives

`DeiFiliusAttributeField` leaves five attributes as explicitly identified
primitives. This module gives two of them a typed sibling reading built from
existing vocabulary, so that most of their content follows from the nine
stage-two attributes and the rest is carried by named open bridges.

**Lord.** LORD_1 is the primitive `Primitives.IsLord` (dominion: authority to
dispose of what is subject to one, after ST I q.13 a.7). LORD_2,
`IsLordByCauseAndGovernment`, reads dominion through its two grounds in the
Summa: g causes the being of everything else (`IsCreatorOfAll`) and governs
everything else (`GovernsAllOthers`, with the q.103 `Governs` relation:
government is directing to an end, q.103 a.3). At a being with the nine:

* the creator conjunct is contained BY DEFINITION in the goodness conjunct
  (`IsSupremelyGood` includes causing every perfection of everything else, so
  its being). That follows from how the case defines supreme goodness. It is not
  an independent derivation of creation;
* the governance conjunct needs the open bridge
  `UniversalIntellectualCauseDirectsAll` (whatever has intellect, has will and
  causes the being of everything else directs each thing to some end; after q.22 a.2's
  reason that the ordering of effects to an end extends as far as the first
  agent's causality) and the existing source reading
  `DirectingToAnEndIsGoverningReading` (q.103 a.3).

Conservation (q.104 a.1) is not a separate conjunct. `CausesIn … esse` has no
time index, so the vocabulary has no typed difference between causing a thing's
being and keeping it in being (per se conservation, definition `56989bd0`, is
itself "without motion or time"); no identification of the two is asserted.
Authority, a right to dispose as distinct from the power to cause and direct, is
not typed either; it is carried by the sense bridge.

**Most blessed.** BLESSED_1 is the primitive `Primitives.MostBlessed`.
BLESSED_2, `IsBlessedByUnderstanding`, reads ST I q.26 a.1–2 (beatitude is the
perfect good of an intellectual nature; it belongs to God by his intellect, in
his act of understanding) with existing vocabulary: g has intellect, is
universally perfect, is good as to being, and is in act in the respect of
understanding (`InAct g understanding`, the primitive respect of definition
`39f50105`, reused from `DeiFiliusOperationFromIntellect`). At a being with the
nine, the first three are among (or inside) the nine, and the fourth follows from
two EXISTING open premises of that module (intellect is the capacity to
understand; that capacity is exercised or in potency) with the nine's pure act:
no new bridge. Not typed: *ex se* (the good is not received from another),
and knowing one's own sufficiency in the good possessed (self-knowledge, q.14
a.2). `InAct` is the nine's formal-or-virtual act (IN_ACT_3), so the fourth
conjunct does not by itself exclude merely virtual understanding. These three
gaps are carried by the sense bridge. BLESSED_1 is read the Thomist way
(beatitude formally in the intellect, q.26 a.2); a Scotist reading (beatitude
formally in the will's enjoyment) would be a further sense, not typed here.

The senses are not identified (invariant 7). Each passage from LORD_2 to LORD_1,
or BLESSED_2 to BLESSED_1, is an explicit sense bridge
(`CauseAndGovernorOfAllIsLord`, `UnderstandingPerfectIsMostBlessed`), each
strictly weaker than the old bridge it replaces in the new routes
(`CreatorOfAllIsLord`, `PerfectIntellectualIsMostBlessed`).

Analyst formulations, attribution deferred: the Summa articles motivate the
readings and bridges; no claim states any of them. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusLordBlessed

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae (DirectingToAnEndIsGoverningReading)
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLivingNineScope (HasTheNine)

/-! ## Lord -/

/-- g governs every other being that is in act as to being, in the q.103 sense
of `Governs` (definition `c53b5fbe`: government directs the governed to an end
consisting in some good). -/
def GovernsAllOthers {Being Respect : Type} (InAct : Being → Respect → Prop) (esse : Respect)
    (Governs : Being → Being → Prop) (g : Being) : Prop :=
  ∀ x, x ≠ g → InAct x esse → Governs g x

/-- LORD_2, *Dominus caeli et terrae* read through its grounds: g causes the being
of everything else and governs everything else. After ST I q.13 a.7 (creatures
are subject to God, as to their cause) and q.103 (God governs all things).
Authority (a right to dispose) is not typed, and conservation has no separate
typed content here (see the module docstring). -/
def IsLordByCauseAndGovernment {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Governs : Being → Being → Prop) (g : Being) : Prop :=
  IsCreatorOfAll InAct CausesIn esse g ∧ GovernsAllOthers InAct esse Governs g

/-- Open bridge: whatever has intellect, has will and causes the being of
everything else directs every other being in act as to being to some end. The
three are separate conjuncts; the antecedent does not say that the being causes
THROUGH its intellect and will (freedom of the act is not encoded). After ST I
q.22 a.2: every agent acts for an end, and the ordering of effects to that end
extends as far as the causality of the first agent extends. That reason
presupposes intellectual, voluntary agency (cf. q.19 a.4), so the bridge also
carries the unstated step that such a being causes through its intellect and
will; the relevant alternative is necessary emanation by an intellect (no
justification on file). Restricted to a cause of the being of ALL others: the
side effects on file involve a particular cause, and their mechanism (according
to q.22 a.2 ad 1, attributed and unpinned: other causes concurring unordered by
it) is absent when one cause gives being to everything else. Nothing is said
about the mode of cognition. -/
def UniversalIntellectualCauseDirectsAll {Being Respect End : Type}
    (InAct : Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (HasIntellect HasWill : Being → Prop)
    (Directs : Being → Being → End → Prop) : Prop :=
  ∀ g, HasIntellect g → HasWill g → IsCreatorOfAll InAct CausesIn esse g →
    ∀ x, x ≠ g → InAct x esse → ∃ e, Directs g x e

/-- Whatever has the nine is LORD_2. Derived (`nineAreLordByCauseAndGovernment`). -/
def NineAreLordByCauseAndGovernment {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop)
    (Governs : Being → Being → Prop) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g → IsLordByCauseAndGovernment InAct CausesIn esse Governs g

/-- Open sense bridge LORD_2 → LORD_1: whatever causes the being of everything else
and governs everything else is lord (has dominion over everything else). After
q.13 a.7: things are subject to God as to their cause. It carries what LORD_2
leaves untyped (authority to dispose); that power-to-authority step is the same
as in the old bridge, only the antecedent is stronger. Strictly weaker than
`CreatorOfAllIsLord` (its antecedent adds governance; `Control.Controls` part 2). -/
def CauseAndGovernorOfAllIsLord {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (Governs : Being → Being → Prop) (D : Primitives Being) : Prop :=
  ∀ g, IsLordByCauseAndGovernment InAct CausesIn esse Governs g → D.IsLord g

/-! ## Most blessed -/

/-- BLESSED_2, *beatissimus* read after ST I q.26 a.1–2: g has intellect, is
universally perfect (PERFECT_2: in act in every respect in which anything is in
act, so no being has a perfection g lacks), is good as to being, and is in act in
the respect of understanding (`InAct g understanding`, definition `39f50105`;
IN_ACT_3, formal or virtual). Not typed: *ex se*, self-knowledge of one's own
sufficiency, and formal (rather than merely virtual) understanding. Read on the
Thomist sense of BLESSED_1 (beatitude formally in the intellect). -/
def IsBlessedByUnderstanding {Being Respect : Type} (InAct GoodIn : Being → Respect → Prop)
    (esse understanding : Respect) (HasIntellect : Being → Prop) (g : Being) : Prop :=
  HasIntellect g ∧ IsPerfect InAct g ∧ GoodIn g esse ∧ InAct g understanding

/-- Whatever has the nine is BLESSED_2. Derived (`nineAreBlessedByUnderstanding`)
from two existing premises of `DeiFiliusOperationFromIntellect`. -/
def NineAreBlessedByUnderstanding {Being Respect : Type}
    (InAct GoodIn InPotency : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse understanding : Respect)
    (IsGod Composite Infinite Eternal HasIntellect HasWill : Being → Prop) : Prop :=
  ∀ g, HasTheNine InAct GoodIn InPotency CausesIn esse IsGod Composite Infinite Eternal
    HasIntellect HasWill g → IsBlessedByUnderstanding InAct GoodIn esse understanding HasIntellect g

/-- Open sense bridge BLESSED_2 → BLESSED_1: whatever has intellect, is universally
perfect, good as to being and in act in understanding has, in and from itself, the
perfect good of an intellectual nature. After q.26 a.1–2. It carries what
BLESSED_2 leaves untyped (*ex se*, knowing its own sufficiency, formal rather than
merely virtual understanding). Strictly weaker than
`PerfectIntellectualIsMostBlessed` (its antecedent adds goodness and act in
understanding; `Control.Controls` part 3). -/
def UnderstandingPerfectIsMostBlessed {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (esse understanding : Respect)
    (HasIntellect : Being → Prop) (D : Primitives Being) : Prop :=
  ∀ g, IsBlessedByUnderstanding InAct GoodIn esse understanding HasIntellect g → D.MostBlessed g

/-! ## Controls -/

namespace Control

open TruthCore.Causality.DeiFiliusLivingNineScope.Control
  (inAct causes noPotency isTrue yes no Nine)

/-- Primitives whose lordship and beatitude are `o` and `b`, the rest false. -/
def prims (o b : Bool → Prop) : Primitives Bool :=
  ⟨fun _ => False, o, fun _ => False, fun _ => False, b⟩

/-- Only `true` causes anything. -/
def causesFromTrue (c _ : Bool) (_ : Unit) : Prop := c = true

def everywhere (_ _ : Bool) : Prop := True
def nowhere (_ _ : Bool) : Prop := False
def directsAll (_ _ : Bool) (_ : Unit) : Prop := True
def directsNone (_ _ : Bool) (_ : Unit) : Prop := False

/-- Two respects: esse (`true`), in which everything is in act, and understanding
(`false`), in which nothing is. -/
def actButNotUnderstanding (_ : Bool) (r : Bool) : Prop := r = true
def causesB (_ _ : Bool) (_ : Bool) : Prop := True
def noPotencyB (_ : Bool) (_ : Bool) : Prop := False

/-- Checked interpretations on two beings (`Bool`; `true` alone is GOD_4 and has
intellect) and one end; nothing is in potency. Parts 1, 2, 4 and 6 have one respect
(`()`, serving as esse and understanding) in which everything is in act; parts 3
and 5 have two respects, esse (`true`), in which everything is in act, and
understanding (`false`), in which nothing is:

1. nonvacuity: with directing and governing everywhere, the directing bridge and
   the q.103 a.3 reading hold, and `true` has the nine, LORD_2 and BLESSED_2;
2. strictness for lord: `true` alone causes, and governs nothing; nothing is
   LORD_1. The new sense bridge holds and `CreatorOfAllIsLord` fails (a cause of
   the being of all that governs nothing is not lord);
3. strictness for blessed: nothing is in act in understanding or BLESSED_1. The new
   sense bridge holds and `PerfectIntellectualIsMostBlessed` fails;
4. the directing bridge is needed: nothing directs or governs; the q.103 a.3
   reading holds, `true` has the nine and is not LORD_2;
5. act in understanding is needed (in the route, the two existing intellect
   premises with pure act supply it): `true` has the nine and is not BLESSED_2;
6. sense-mixing control: with nothing LORD_1 or BLESSED_1, `true` has the nine and
   is LORD_2 and BLESSED_2 without being LORD_1 or BLESSED_1. -/
def Controls : Prop :=
  (UniversalIntellectualCauseDirectsAll inAct causes () isTrue yes directsAll ∧
    DirectingToAnEndIsGoverningReading directsAll everywhere ∧
    Nine isTrue true ∧ IsLordByCauseAndGovernment inAct causes () everywhere true ∧
    IsBlessedByUnderstanding inAct inAct () () isTrue true) ∧
  (CauseAndGovernorOfAllIsLord inAct causesFromTrue () nowhere (prims no no) ∧
    ¬ CreatorOfAllIsLord inAct causesFromTrue () (prims no no)) ∧
  (UnderstandingPerfectIsMostBlessed actButNotUnderstanding actButNotUnderstanding true false
      isTrue (prims no no) ∧
    ¬ PerfectIntellectualIsMostBlessed actButNotUnderstanding isTrue (prims no no)) ∧
  (DirectingToAnEndIsGoverningReading directsNone nowhere ∧ Nine isTrue true ∧
    ¬ IsLordByCauseAndGovernment inAct causes () nowhere true) ∧
  (HasTheNine actButNotUnderstanding actButNotUnderstanding noPotencyB causesB true isTrue no
      yes yes isTrue yes true ∧
    ¬ IsBlessedByUnderstanding actButNotUnderstanding actButNotUnderstanding true false
      isTrue true) ∧
  (Nine isTrue true ∧ IsLordByCauseAndGovernment inAct causes () everywhere true ∧
    IsBlessedByUnderstanding inAct inAct () () isTrue true ∧
    ¬ (prims no no).IsLord true ∧ ¬ (prims no no).MostBlessed true)

end Control
end TruthCore.Causality.DeiFiliusLordBlessed
