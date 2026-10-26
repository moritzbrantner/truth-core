import TruthCore.Case.Catholicism.StageOneQuartaVia

/-!
Stage 2, the classical divine attributes (owner decision on #143, 2026-10-24:
option (a)). The skeleton keeps its field `HasClassicalAttributes`. One open
definitional bridge, sourced from Vatican I, *Dei Filius* ch. 1, says which
attributes it abbreviates. Each attribute is then derived for God, one group at a
time, from ST I qq.3–26.

The link from the skeleton's `IsGod` to the *quarta via* is the converse of the
nominal definition: whatever is God is maximal in being (`GodIsMaximalInBeing`,
open, supported by q.13 a.8 ad 2 *supra omnia existens* and *Dei Filius* ch. 1
*super omnia … excelsus*).

Group 1 (this module's derived attributes): one, simple, perfect, supremely good.
The other five (infinite, immutable, eternal, intellect, will) are derived in
groups 2 and 3 (results CATHOLICISM-STAGE2-GOD-IS-INFINITE … -HAS-WILL), each
also supported by *Dei Filius* ch. 1.
-/

namespace TruthCore.Case.Catholicism

open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn)

universe u v

/-- The definitional bridge: a being that is simple, perfect, good, one,
infinite, immutable, eternal, and has intellect and will has the classical
attributes. Open premise. It fixes what the skeleton field abbreviates, after
*Dei Filius* ch. 1 (*unum … aeternum, immensum … intellectu ac voluntate omnique
perfectione infinitum … simplex omnino et incommutabilis*). -/
def ClassicalAttributesSuffice (σ : Signature)
    (Simple Perfect Good One Infinite Immutable Eternal HasIntellect HasWill :
      σ.Being → Prop) : Prop :=
  ∀ g, Simple g → Perfect g → Good g → One g → Infinite g → Immutable g → Eternal g →
    HasIntellect g → HasWill g → σ.HasClassicalAttributes g

/-- Whatever is God is maximal in being. Open premise: the converse of the nominal
definitions of stage 1, read as a definite description (the name applies only to
what fits it). -/
def GodIsMaximalInBeing {Being : Sort u} {Respect : Sort v}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ g, IsGod g → IsMaximumIn InAct MoreIn esse g

/-- `g` is the one God: whatever is God is `g`. -/
def IsTheOneGod {Being : Sort u} (IsGod : Being → Prop) (g : Being) : Prop :=
  ∀ g', IsGod g' → g' = g

/-- `g` is simple: it is not composite in any way (ST I q.3 a.7). -/
def IsSimple {Being : Sort u} (Composite : Being → Prop) (g : Being) : Prop :=
  ¬ Composite g

/-- `g` is perfect: whatever any being is in act in, `g` is in act in, formally or
eminently (ST I q.4 a.2, *universaliter perfectus*). -/
def IsPerfect {Being : Sort u} {Respect : Sort v} (InAct : Being → Respect → Prop)
    (g : Being) : Prop :=
  ∀ x r, InAct x r → InAct g r

/-- `g` is supremely good: good in respect of being (ST I q.5 a.1) and the cause
from which every perfection of other things flows (ST I q.6 a.2, *summum bonum
… inquantum omnes perfectiones desideratae effluunt ab eo, sicut a prima
causa*). -/
def IsSupremelyGood {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) (g : Being) : Prop :=
  GoodIn g esse ∧ CausesEveryPerfectionOfOthers InAct CausesIn g

/-- God is one: any two beings that are God are the same. -/
def GodIsOne {Being : Sort u} (IsGod : Being → Prop) : Prop :=
  ∀ g, IsGod g → IsTheOneGod IsGod g

/-- God is simple. -/
def GodIsSimple {Being : Sort u} (IsGod Composite : Being → Prop) : Prop :=
  ∀ g, IsGod g → IsSimple Composite g

/-- God is perfect. -/
def GodIsPerfect {Being : Sort u} {Respect : Sort v} (IsGod : Being → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ g, IsGod g → IsPerfect InAct g

/-- God is supremely good. -/
def GodIsSupremelyGood {Being : Sort u} {Respect : Sort v} (IsGod : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g, IsGod g → IsSupremelyGood InAct GoodIn CausesIn esse g

/-- God is infinite (ST I q.7). Derived in result CATHOLICISM-STAGE2-GOD-IS-INFINITE;
`Infinite` is fixed by its attribute group. -/
def GodIsInfinite {Being : Sort u} (IsGod Infinite : Being → Prop) : Prop :=
  ∀ g, IsGod g → Infinite g

/-- God is immutable (ST I q.9). Derived in result CATHOLICISM-STAGE2-GOD-IS-IMMUTABLE. -/
def GodIsImmutable {Being : Sort u} (IsGod Immutable : Being → Prop) : Prop :=
  ∀ g, IsGod g → Immutable g

/-- God is eternal (ST I q.10). Derived in result CATHOLICISM-STAGE2-GOD-IS-ETERNAL. -/
def GodIsEternal {Being : Sort u} (IsGod Eternal : Being → Prop) : Prop :=
  ∀ g, IsGod g → Eternal g

/-- God has intellect (ST I q.14). Derived in result CATHOLICISM-STAGE2-GOD-HAS-INTELLECT. -/
def GodHasIntellect {Being : Sort u} (IsGod HasIntellect : Being → Prop) : Prop :=
  ∀ g, IsGod g → HasIntellect g

/-- God has will (ST I q.19). Derived in result CATHOLICISM-STAGE2-GOD-HAS-WILL. -/
def GodHasWill {Being : Sort u} (IsGod HasWill : Being → Prop) : Prop :=
  ∀ g, IsGod g → HasWill g

/-! ## Group 2: infinite, immutable, eternal (ST I qq.7, 9, 10) -/

/-- `g` is altogether immutable: it is in potency in no respect, so it has no
capacity for any change (ST I q.9 a.1: whatever is changed in any way is in some
way in potency). Not merely "not changing now" (Codex P1 on #199). -/
def IsImmutable {Being : Sort u} {Respect : Sort v} (InPotency : Being → Respect → Prop)
    (g : Being) : Prop :=
  ∀ r, ¬ InPotency g r

end TruthCore.Case.Catholicism
