module

public import TruthCore.Causality.NecessaryClassicalGodRoot
public import TruthCore.Causality.NamingVeracityBatch1

/-! The classical attributes defined from Vatican I, *Dei Filius* ch. 1
(DS 3001–3002), in place of the primitive skeleton field as the target of the
stage-two sufficiency premise.

`Signature.HasClassicalAttributes` stays a primitive field (changing the
skeleton would break every frozen Challenge that uses it). This module adds a
*defined* predicate, `DeiFiliusAttributes`, whose conjuncts are typed attribute
predicates read off the attribute list recorded in claim
`VATICAN-I-DEI-FILIUS-CH1-ONE-TRUE-LIVING-GOD`, reusing existing case
vocabulary where it exists. Two open premises connect it to the old premise
`ClassicalAttributesSuffice`:

* `NineSufficeForDeiFilius`: the nine stage-two predicates give every Dei Filius
  conjunct (the restated sufficiency, against the defined predicate);
* `FieldFromDeiFilius`: whatever has every Dei Filius conjunct has the
  primitive field (one reading of the field; strictly weaker than the old
  premise).

The primitive field itself stays undefined, and its intended content is an
interpretation fork (`CLASSICAL_FIELD`). `Root.lean` documents it as "intended
to group simplicity, perfection, goodness, infinity, immutability, eternity,
unity, intellect and will", exactly the nine (CLASSICAL_FIELD_1); the Dei Filius
motivation is in `ClassicalAttributesSuffice`'s docstring, in
`DEF-CLASSICAL-ATTRIBUTES-BUNDLE` and in the claim. On the nine-reading the old
premise is close to analytic, `FieldFromDeiFilius` follows at once and the
bridges below do no work for sufficiency. On the full-list reading
(CLASSICAL_FIELD_2, `DeiFiliusAttributes`) the bridges carry the warrant.

Analyst formulations, attribution deferred (owner direction 2026-11-05): the
claim motivates the list; no claim here states any bridge. Readings and their
gaps (for example, "creator" is causing the being of everything else, not
creation from nothing) are stated at each definition.

Five attributes are explicitly identified PRIMITIVES, bundled in `Primitives`:
living, lord, immense, incomprehensible and most blessed. Each has a stated
meaning and an open bridge from typed attributes, after the Summa's own reason
for it; nothing constrains the primitive beyond that bridge. For living the
corpus already has a typed, time-indexed route (`SelfOperationLife`: life as
self-operation, derived for pure act as `∃ t, LivesAt x t` in a duration
frame). It is kept as the sibling reading LIVING_2 (`LivesSomeTime`), not
reused: it adds a duration frame and a primitive `Operates` to the attribute
vocabulary, and identifying its time-indexed life with the timeless `Lives`
would merge two senses (invariant 7). Composing the two needs an explicit
bridge, not definitional identity. -/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusAttributeField

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)

/-- Explicitly identified primitive attribute predicates (Encode first: a
primitive must be named as such, with its meaning and open obligations).

* `Lives g` — *vivus* (LIVING_1): g lives, i.e. operates from itself and not as
  moved by another (`DEF-LIVING`, ST I q.18 a.3). Timeless; distinct from life
  present at some time of a duration frame (LIVING_2, `LivesSomeTime`,
  `DEF-LIFE-PRESENT-AT`). Open obligation: a typed account of operating from
  oneself that applies to an immutable being.
* `IsLord g` — *Dominus caeli et terrae*: g has dominion over everything else
  (ST I q.13 a.7: "Lord" is said of God relative to creatures). Open
  obligation: a typed account of dominion (authority to dispose of what is
  subject to one).
* `Immense g` — *immensus*: g is measured or contained by no place and is
  present to everything that is (ST I q.8). Open obligation: a typed account
  of presence to things and of place.
* `Incomprehensible g` — *incomprehensibilis*: no created intellect knows g as
  perfectly as g is knowable (ST I q.12 a.7). Open obligation: typed created
  intellects and a measure of knowability.
* `MostBlessed g` — *in se et ex se beatissimus*: g has, in and from itself,
  the perfect good of an intellectual nature (ST I q.26 a.1). Open obligation:
  a typed account of beatitude.

No field is constrained by an axiom; the five open bridges below are the only
constraints anything here places on them. -/
structure Primitives (Being : Type) where
  Lives : Being → Prop
  IsLord : Being → Prop
  Immense : Being → Prop
  Incomprehensible : Being → Prop
  MostBlessed : Being → Prop

/-- LIVING_2, the sibling time-indexed reading of *vivus*: g's life is present at
some time of a duration frame (`DEF-LIFE-PRESENT-AT`). This is the conclusion
shape of the existing route `SelfOperationLife` (result
`PURE-ACT-LIVES-FROM-SELF-OPERATION`, statement `STMT-PURE-ACT-LIVES`). It is
not a field of `DeiFiliusAttributes`, and nothing here relates it to the timeless
`Primitives.Lives` (LIVING_1). -/
def LivesSomeTime {Being Time : Type} (LivesAt : Being → Time → Prop) (g : Being) : Prop :=
  ∃ t, LivesAt g t

/-- *Creator caeli et terrae*, weakest typed reading: g causes the being of
everything other than g that is in act as to being. Not encoded: creation
from nothing (no presupposed subject), freedom of the act, and a beginning.
"Heaven and earth" is read as everything else in the `Being` domain. -/
def IsCreatorOfAll {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (g : Being) : Prop :=
  ∀ x, x ≠ g → InAct x esse → CausesIn g x esse

/-- *Omnipotens*: g can do every task that involves no contradiction (ST I q.25
a.3), in the existing `Power` vocabulary (`DEF-ACTIVE-POWER-TASK-VOCABULARY`);
the body of `GodIsOmnipotent` at one being. -/
def IsAlmighty (σ : Signature) (P : Power σ) (g : σ.Being) : Prop :=
  ∀ t, P.Consistent t → P.CanDo g t

/-- *Spiritualis*, weakest typed reading: g is not composed of matter and form
(ST I q.3 a.2). With `RemoteFromAll` (the distinctness conjunct) it is the
existing altogether-immaterial antecedent (`DEF-ALTOGETHER-IMMATERIAL`).
*Substantia* (subsisting rather than inhering) is not typed here: on its own
`IsSpiritual` is also satisfied by prime matter or an accident (neither is
composed of matter and form), which only the `distinct` conjunct excludes
jointly. -/
def IsSpiritual {Being : Type} (MatterForm : Being → Prop) (g : Being) : Prop :=
  ¬ MatterForm g

/-- The attributes confessed of God in *Dei Filius* ch. 1 (DS 3001), with
goodness from DS 3002 (*bonitate sua*), as one defined predicate of a being, in
the typed reading of definition `edcfac86`: some fields are weaker than the
text, one is stronger (`good`) and one is a different reading (`distinct`).
Each field is a typed predicate or an explicitly identified primitive:

* `one` — *unus … una singularis*: `IsTheOneGod σ.IsGod` (`DEF-ONE-GOD`);
* `living` — *vivus*: primitive `Lives` (LIVING_1);
* `creator` — *creator caeli et terrae*: `IsCreatorOfAll` (no creation ex
  nihilo); contained by definition in the `good` field;
* `lord` — *Dominus*: primitive `IsLord`;
* `almighty` — *omnipotens*: `IsAlmighty`;
* `eternal` — *aeternus*: `Eternal` (ETERNAL_1);
* `immense` — *immensus*: primitive `Immense`;
* `incomprehensible` — *incomprehensibilis*: primitive `Incomprehensible`;
* `intellect`, `will`, `perfect`, `infinite` — *intellectu ac voluntate
  omnique perfectione infinitus*, read as the conjunction HAS_INTELLECT_1,
  HAS_WILL_1, PERFECT_2 and INFINITE_1. Weaker than "infinite in intellect and
  will": the infinity of intellect and of will as such is not typed;
* `simple` — *simplex omnino*: `IsSimple` (SIMPLE_4);
* `immutable` — *incommutabilis*: `IsImmutable` (IMMUTABLE_1, pure act);
* `spiritual` — *substantia spiritualis*: `IsSpiritual` (substance not typed);
* `distinct` — *re et essentia a mundo distinctus*: a DIFFERENT reading,
  `RemoteFromAll` (`DEF-REMOTE-FROM-ALL`), g enters into the composition of
  nothing. The two are incomparable: the anti-pantheist content of DS 3001 and
  canons DS 3023–3024 (numerical non-identity with the world as a whole, and
  distinctness *in essence*) is not typed, since the signature has no term for
  the world; and a Spinozist God, which is no part, matter or form of its
  modes, satisfies `RemoteFromAll`;
* `blessed` — *beatissimus*: primitive `MostBlessed`;
* `exalted` — *super omnia … excelsus*: `IsMaximumIn InAct MoreIn esse`
  (MAXIME_ENS_1: in act as to being, and nothing is more in being). Weaker
  than exceeding everything else; *ineffabiliter* and "above all that can be
  conceived" are not typed;
* `good` — *bonitate sua*: `IsSupremelyGood` (`DEF-SUPREMELY-GOOD`). A
  STRENGTHENING: DS 3002 names God's goodness as the motive of creation, while
  `IsSupremelyGood` also includes causing every perfection of everything else
  (q.6 a.2), which is why `creator` follows from it by definition.

`almighty` is active power (`DEF-ACTIVE-POWER-TASK-VOCABULARY`); `immutable` is
the absence of passive potency (`InPotency`, `DISAMB-POTENCY`). They use different
notions, so having both is no sense clash.

*Verus* (true God, as against false gods) is not a field: it is the predicate
`σ.IsGod` of which the attributes are confessed, kept as its own conjunct
wherever the attributes are predicated of God. -/
structure DeiFiliusAttributes (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) (g : σ.Being) : Prop where
  one : IsTheOneGod σ.IsGod g
  living : D.Lives g
  creator : IsCreatorOfAll InAct CausesIn esse g
  lord : D.IsLord g
  almighty : IsAlmighty σ P g
  eternal : Eternal g
  immense : D.Immense g
  incomprehensible : D.Incomprehensible g
  intellect : HasIntellect g
  will : HasWill g
  perfect : IsPerfect InAct g
  infinite : Infinite g
  simple : IsSimple Composite g
  immutable : IsImmutable InPotency g
  spiritual : IsSpiritual MatterForm g
  distinct : RemoteFromAll ComponentOf g
  blessed : D.MostBlessed g
  exalted : IsMaximumIn InAct MoreIn esse g
  good : IsSupremelyGood InAct GoodIn CausesIn esse g

/-- The nine stage-two predicates are among the Dei Filius conjuncts: a
projection, by structure fields. No philosophical inference. -/
theorem nineOfDeiFilius (σ : Signature) {Respect : Type}
    {InAct GoodIn InPotency : σ.Being → Respect → Prop}
    {CausesIn : σ.Being → σ.Being → Respect → Prop} {esse : Respect}
    {MoreIn : Respect → σ.Being → σ.Being → Prop} {ComponentOf : σ.Being → σ.Being → Prop}
    {Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop}
    {P : Power σ} {D : Primitives σ.Being} {g : σ.Being}
    (h : DeiFiliusAttributes σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D g) :
    NineClassicalAttributes (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill g :=
  ⟨h.simple, h.perfect, h.good, h.one, h.infinite, h.immutable, h.eternal, h.intellect, h.will⟩

/-! ## The two premises that replace the stipulated sufficiency -/

/-- The restated sufficiency premise, against the defined predicate: every being
with the nine stage-two attributes has every Dei Filius attribute. Open premise;
derived from typed bridges in `nineGiveDeiFilius`. -/
def NineSufficeForDeiFilius (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) : Prop :=
  ∀ g, NineClassicalAttributes (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill g →
    DeiFiliusAttributes σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D g

/-- The field interpretation on the full-list reading (CLASSICAL_FIELD_2): whatever
has every Dei Filius attribute, as typed here, has the skeleton's
`HasClassicalAttributes`. Open premise, one-way, with no converse. It is not
what `Root.lean` documents: there the field is "intended to group simplicity,
perfection, goodness, infinity, immutability, eternity, unity, intellect and
will", the nine (CLASSICAL_FIELD_1); Dei Filius ch. 1 motivates
`ClassicalAttributesSuffice` and `DEF-CLASSICAL-ATTRIBUTES-BUNDLE`. On the
nine-reading this premise follows at once. It is strictly weaker than the old
sufficiency premise: the results module's `fieldOfSuffice` (lake-checked, not a
registered result, so not Comparator-verified) and `Control.Controls` part 3. -/
def FieldFromDeiFilius (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being) : Prop :=
  ∀ g, DeiFiliusAttributes σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D g →
    σ.HasClassicalAttributes g

/-! ## Open bridges, one per conjunct the nine do not give by definition

Analyst formulations after the Summa's reason for each attribute, attribution
deferred. Each states one mechanism and can fail (`Control`). -/

/-- Open bridge (*vivus*): whatever has intellect lives. After ST I q.18 a.3:
understanding is the highest grade of life, and life is grounded in intellect,
not in the bare absence of potency (compare `STMT-PURE-ACT-LIVES`, which is
time-indexed, and `STMT-THINKER-LIVES`, which concerns occurring thoughts;
neither is identified with this bridge). -/
def IntellectualIsLiving {Being : Type} (HasIntellect : Being → Prop) (D : Primitives Being) :
    Prop :=
  ∀ g, HasIntellect g → D.Lives g

/-- Open bridge (*Dominus*): whatever causes the being of everything else is
lord of everything else. After ST I q.13 a.7 ("Lord" is said relative to
creatures, which are subject to God as their cause). -/
def CreatorOfAllIsLord {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (D : Primitives Being) : Prop :=
  ∀ g, IsCreatorOfAll InAct CausesIn esse g → D.IsLord g

/-- Open bridge (*immensus*): whatever causes the being of everything else is
immense. After ST I q.8 a.1–2: God is in all things as an agent is present to
its effect, and in every place by giving it being. -/
def CreatorOfAllIsImmense {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (D : Primitives Being) : Prop :=
  ∀ g, IsCreatorOfAll InAct CausesIn esse g → D.Immense g

/-- Open bridge (*incomprehensibilis*): whatever is infinite (INFINITE_1) is
incomprehensible. After ST I q.12 a.7: no created intellect comprehends God,
because God is infinitely knowable and a created intellect knows finitely. -/
def InfiniteIsIncomprehensible {Being : Type} (Infinite : Being → Prop) (D : Primitives Being) :
    Prop :=
  ∀ g, Infinite g → D.Incomprehensible g

/-- Open bridge (*beatissimus*): whatever is universally perfect and has
intellect is most blessed. After ST I q.26 a.1: beatitude is the perfect good
of an intellectual nature, and it belongs to God in the highest degree. -/
def PerfectIntellectualIsMostBlessed {Being Respect : Type} (InAct : Being → Respect → Prop)
    (HasIntellect : Being → Prop) (D : Primitives Being) : Prop :=
  ∀ g, IsPerfect InAct g → HasIntellect g → D.MostBlessed g

/-- Open bridge (*a mundo distinctus*, via q.3 a.8): whatever causes the being of
everything else enters into the composition of nothing. After ST I q.3 a.8's
reason that the first efficient cause is not numerically one with the form or
matter of what it makes. Q.3 a.8 itself reports three contrary positions: God as
world-soul (via Augustine, *De civ. Dei* VII), God as the formal principle of all
things (the Amalricians) and God as prime matter (David of Dinant). Obj. 1 cites
Dionysius: the being of all is the deity, and the being of all enters each
composite. The Amalrician position and obj. 1 grant that God gives being and deny
this consequent; Aquinas replies (ad 1) that deity is the being of all
effectively and exemplarily, not by essence. -/
def CreatorOfAllIsNoComponent {Being Respect : Type} (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ g, IsCreatorOfAll InAct CausesIn esse g → RemoteFromAll ComponentOf g

/-- Open bridge (*excelsus*): to be more in being than x is to be in act in some
respect in which x is not. After the reading of grades of being as grades of
act (ST I q.4 a.2, q.2 a.3 *quarta via*). Interpretation gap: with a binary
`InAct`, two things in act in the same respects cannot differ in being; a
reading on which grades are intensities of one act (more of the same
perfection) makes this bridge fail unless respects are fine-grained enough to
separate grades. -/
def ExcessInBeingIsExcessInAct {Being Respect : Type} (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ y x, MoreIn esse y x → ∃ r, InAct y r ∧ ¬ InAct x r

/-! ## The defined endpoint at the spine's root -/

/-- `NecessaryClassicalGodRootAt` with the primitive field replaced by the
defined Dei Filius attributes: ONE actual selected necessary root retains
maximum/perfection, represented esse/essence identity, firstness, matter-form
exclusion and remoteness, is God (GOD_4) and has every Dei Filius attribute
(which include the nine). Selected-root uniqueness is not uniqueness of all
necessary individuals. -/
def NecessaryDeiFiliusGodRootAt {W P R : Type} (σ : Signature)
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being P R)
    (GoodIn InPotency : σ.Being → R → Prop) (MoreIn : R → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being) : Prop :=
  ∃ n, TruthCore.Causality.DirectEsseRootPerfectionGoodness.PerfectRootAt m w p.InAct MoreIn p.esse n ∧
    p.esseOf n = p.essenceOf n ∧ IsFirstBeing PriorSimply n ∧
    ¬ MatterForm n ∧ RemoteFromAll ComponentOf n ∧ σ.IsGod n ∧
    DeiFiliusAttributes σ p.InAct GoodIn InPotency p.CausesIn p.esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D n

/-! ## Controls -/

namespace Control

/-- A one-being signature whose single being is God; `field` is the primitive
classical field. -/
def sig (field : Prop) : Signature where
  Being := Unit
  IsGod _ := True
  HasClassicalAttributes _ := field
  RevealsRecognizably _ := True
  jesus := ()
  ClaimedDivineAuthority _ := True
  RoseFromTheDead _ := True
  Society := Unit
  catholicChurch := ()
  Founded _ _ := True
  VisibleWithAuthority _ := True
  FoundedAsTeachingAuthority _ _ := True
  DefinitivelyProposesAsRevealed _ _ := True
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

/-- Power over one consistent task, which the one being can do iff `can`. -/
def power (field can : Prop) : Power (sig field) where
  Task := Unit
  revealWithSigns := ()
  Consistent _ := True
  CanDo _ _ := can
  Perfection := Unit
  Requires _ _ := True
  InAct _ _ := can
  PossibleAct _ := True

/-- Primitives with the five truth values given. -/
def prims (l o i c b : Prop) : Primitives Unit :=
  ⟨fun _ => l, fun _ => o, fun _ => i, fun _ => c, fun _ => b⟩

/-- Truth values fixing one one-being interpretation: `field` the primitive
field, `can` whether the being can do the one consistent task, `l o i c b` the
five primitives, `more` whether the being is more in being than itself, `comp`
whether it is a component of itself, `matter` whether it is composed of matter
and form, `composite` whether it is composite. Respects and principles are
`Unit`; the being is in act, good and causing in every respect and in potency in
none; infinite, eternal, intellect and will are true. -/
structure Case where
  field : Prop
  can : Prop
  l : Prop
  o : Prop
  i : Prop
  c : Prop
  b : Prop
  more : Prop
  comp : Prop
  matter : Prop
  composite : Prop

/-- All premises of `nineGiveDeiFilius` except the one numbered `skip` (0 living,
1 lord, 2 almighty, 3 immense, 4 incomprehensible, 5 blessed, 6 no component,
7 excess in act, 8 matter-form composition; any other number omits none), at
the interpretation of `k`. -/
def Premises (k : Case) (skip : Nat) : Prop :=
  let σ := sig k.field
  let T : σ.Being → Prop := fun _ => True
  let InAct : σ.Being → Unit → Prop := fun _ _ => True
  let CausesIn : σ.Being → σ.Being → Unit → Prop := fun _ _ _ => True
  let D := prims k.l k.o k.i k.c k.b
  (skip ≠ 0 → IntellectualIsLiving T D) ∧
  (skip ≠ 1 → CreatorOfAllIsLord InAct CausesIn () D) ∧
  (skip ≠ 2 → InfiniteActHasInfinitePower σ T (power k.field k.can)) ∧
  (skip ≠ 3 → CreatorOfAllIsImmense InAct CausesIn () D) ∧
  (skip ≠ 4 → InfiniteIsIncomprehensible T D) ∧
  (skip ≠ 5 → PerfectIntellectualIsMostBlessed InAct T D) ∧
  (skip ≠ 6 → CreatorOfAllIsNoComponent InAct CausesIn () (fun _ _ => k.comp)) ∧
  (skip ≠ 7 → ExcessInBeingIsExcessInAct InAct (fun _ _ _ => k.more) ()) ∧
  GoodnessIsActualityReading (fun (_ : σ.Being) (_ : Unit) => True) InAct ∧
  (skip ≠ 8 → MatterFormAndEsseEssenceAreCompositionsReading (fun _ => k.matter)
    (fun _ => k.composite) (fun (_ : σ.Being) => ()) (fun _ => ()))

/-- The nine stage-two attributes at the one being of `k`. -/
def Nine (k : Case) : Prop :=
  NineClassicalAttributes (IsSimple (fun (_ : (sig k.field).Being) => k.composite))
    (IsPerfect (fun _ (_ : Unit) => True))
    (IsSupremelyGood (fun _ (_ : Unit) => True) (fun _ _ => True) (fun _ _ _ => True) ())
    (IsTheOneGod (sig k.field).IsGod) (fun _ => True) (IsImmutable (fun _ (_ : Unit) => False))
    (fun _ => True) (fun _ => True) (fun _ => True) ()

/-- The Dei Filius attributes at the one being of `k`. -/
def DF (k : Case) : Prop :=
  DeiFiliusAttributes (sig k.field) (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
    (fun _ _ _ => True) () (fun _ _ _ => k.more) (fun _ _ => k.comp) (fun _ => k.composite)
    (fun _ => k.matter) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
    (power k.field k.can) (prims k.l k.o k.i k.c k.b) ()

/-- The baseline case: everything holds (field true). -/
def full : Case := ⟨True, True, True, True, True, True, True, False, False, False, False⟩

/-- `full` with one primitive or relation changed, for the control of premise `k`. -/
def omitCase : Nat → Case
  | 0 => { full with l := False, field := False }
  | 1 => { full with o := False }
  | 2 => { full with can := False }
  | 3 => { full with i := False }
  | 4 => { full with c := False }
  | 5 => { full with b := False }
  | 6 => { full with comp := True }
  | 7 => { full with more := True }
  | 8 => { full with matter := True }
  | _ => full

/-- The control statement: (1) nonvacuity: in `full` every premise of
`nineGiveDeiFilius` holds and the one being has the nine and every Dei Filius
attribute; (2) for each premise numbered 0–8, in `omitCase k` every other
premise holds and the one being has the nine but not every Dei Filius
attribute; (3) in `omitCase 0` the field interpretation `FieldFromDeiFilius`
holds while the old sufficiency premise fails. Statements about these
interpretations only. -/
def Controls : Prop :=
  (Premises full 99 ∧ Nine full ∧ DF full) ∧
  (∀ k, k < 9 → Premises (omitCase k) k ∧ Nine (omitCase k) ∧ ¬ DF (omitCase k)) ∧
  (FieldFromDeiFilius (sig False) (fun _ _ => True) (fun _ _ => True) (fun _ _ => False)
      (fun _ _ _ => True) () (fun _ _ _ => False) (fun _ _ => False) (fun _ => False)
      (fun _ => False) (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True)
      (power False True) (prims False True True True True) ∧
    ¬ ClassicalAttributesSuffice (sig False) (IsSimple (fun _ => False))
      (IsPerfect (fun _ (_ : Unit) => True))
      (IsSupremelyGood (fun _ (_ : Unit) => True) (fun _ _ => True) (fun _ _ _ => True) ())
      (IsTheOneGod (sig False).IsGod) (fun _ => True) (IsImmutable (fun _ (_ : Unit) => False))
      (fun _ => True) (fun _ => True) (fun _ => True))

end Control

end TruthCore.Causality.DeiFiliusAttributeField
