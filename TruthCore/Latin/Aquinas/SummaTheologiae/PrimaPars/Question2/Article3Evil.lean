/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.2 a.3:
the thesis of the article, the first objection (the argument from evil) and
its reply.

Vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over.
* `God g`, `SupremelyGood g`, `Omnipotent g` — `g` is God, supremely good,
  omnipotent.
* `Evil x` — there is evil in `x`.
* `Perfection`, `GoodIn y p` — perfections, and `y` being good in respect of
  `p` (as in I q.5 a.1).
* `DrawsGoodFrom g x y p` — `g` brings the good of `p` in `y` out of the evil
  in `x` (as the lion's life is preserved through the ass's death, q.48 a.2
  ad 3).
* `Sentence`, `Holds φ`, `evilPremise` — sentences, truth, and the sentence
  "there is evil in the world".

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q2-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- The objector's premise that there is evil in the world
(*invenitur autem malum in mundo*), asserted as true.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 obj. 1.
-/
def EvilPremiseAssertedReading {Sentence : Sort w}
    (Holds : Sentence → Prop) (evilPremise : Sentence) : Prop :=
  Holds evilPremise

/-- The first objection's conditional: if God existed, no evil would be found
(*si ergo Deus esset, nullum malum inveniretur*), because if one of two
contraries were infinite, the other would be wholly destroyed, and the name
"God" signifies an infinite good.

Only the conditional is formalized, not the contrariety principle behind it.
Aquinas states this objection in order to answer it; the claim records what
the objection says.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 obj. 1.
-/
def GodWouldExcludeAllEvilObjectionReading {Being : Sort u}
    (God Evil : Being → Prop) : Prop :=
  ∀ g, God g → ¬ ∃ x, Evil x

/-- God is supremely good and omnipotent: the reply, quoting Augustine,
speaks of God "since he is supremely good" (*cum sit summe bonus*) and "so
omnipotent and good" (*adeo omnipotens et bonus*).

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 ad 1.
-/
def GodSupremelyGoodAndOmnipotentReading {Being : Sort u}
    (God SupremelyGood Omnipotent : Being → Prop) : Prop :=
  ∀ g, God g → SupremelyGood g ∧ Omnipotent g

/-- For every evil there is, God brings some good out of it. Read from: God
permits evil only so as to bring good out of it: God, being supremely
good, "would in no way allow any evil in his works unless he were so
omnipotent and good as to bring good even out of evil"; "it belongs to the
infinite goodness of God that he permit evils to be, and draw goods from them"
(*ut esse permittat mala, et ex eis eliciat bona*).

Read per evil: for every evil there is, God brings out of it some good,
namely some being's being good in some perfection (`GoodIn` is a parameter
here; this reading does not tie it to being in act).
This is a disputed strengthening: the coordinated subjunctives in ad 1 do
not themselves assert an actual good token for every evil. The conditional
collective policy and capability siblings below preserve separate scopes.
No implication between their different relation parameters is supplied. The reading does not say that the good
outweighs the evil, nor that it goes to the one who suffers the evil.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 ad 1.
-/
def GodDrawsGoodFromEveryEvilReading {Being : Sort u} {Perfection : Sort v}
    (God Evil : Being → Prop) (GoodIn : Being → Perfection → Prop)
    (DrawsGoodFrom : Being → Being → Being → Perfection → Prop) : Prop :=
  ∀ g x, God g → Evil x → ∃ y p, GoodIn y p ∧ DrawsGoodFrom g x y p

/-- Collective policy reading of ad 1's final sentence (reading B).

The fixed predicate `Evil` picks out the evils in the works under consideration;
`PermitsEvils g Evil` says that `g` allows that collection to be. If it is
nonempty and permitted, `g` actually draws some good from it taken together.
`DrawsGoodFromEvils` takes the entire predicate, not an individual evil-bearing
subject. No universal quantifier distributes the good over that collection,
and no quantifier ranges over arbitrary subcollections.

Source: ST I q.2 a.3 ad 1, pinned passage `AQUINAS-ST-I-Q2-A3`, final sentence:
*ad infinitam Dei bonitatem pertinet, ut esse permittat mala, et ex eis eliciat
bona*. `Permittat` and `eliciat` are coordinated subjunctives dependent on
*pertinet ut*. The actual-production consequent is an interpretive policy
construal of this clause, not an indicative assertion of any token good or
permission. A capability-only extraction of the preceding quotation is kept
separately below. This conditional does not assert God, evil or permission
exists, a net benefit, a best world, or justification of every evil.

All relations are parameters. In particular this definition neither identifies
`GoodIn` with being in act (q.5 a.1), nor derives a productive relation from
permission, nor equates this collective relation with the per-evil relation.
-/
def GodDrawsGoodFromPermittedEvilsCollectivelyReading
    {Being : Type u} {Perfection : Type v}
    (God Evil : Being → Prop) (GoodIn : Being → Perfection → Prop)
    (PermitsEvils : Being → (Being → Prop) → Prop)
    (DrawsGoodFromEvils : Being → (Being → Prop) → Being → Perfection → Prop) : Prop :=
  ∀ g, God g → PermitsEvils g Evil → (∃ x, Evil x) →
    ∃ y p, GoodIn y p ∧ DrawsGoodFromEvils g Evil y p

/-- Collective capability condition on permission (reading C).

Source: ST I q.2 a.3 ad 1, pinned passage `AQUINAS-ST-I-Q2-A3`, Augustine
quotation: *nullo modo sineret aliquid mali esse in operibus suis, nisi esset
adeo omnipotens et bonus, ut bene faceret etiam de malo*.

Only a necessary capability condition is extracted: if God permits the
nonempty fixed collection of evils, he can bring some good from it. The generic
*de malo* is taken collectively; neither each evil nor each subset is
quantified over. This is not the full counterfactual/modal structure of
*sineret ... nisi esset ... faceret*, nor an assertion of the attributes.

`CanDrawGoodFromEvils` is a primitive capability predicate. It does not require
an actual `GoodIn` witness or productive event. No rule connecting it with the
actual productive relations is assumed. Thus neither actual production of
good, the occurrence of permission, existence of God/evil, net benefit, a best
world nor justification of each evil is asserted by this reading.
-/
def GodCanDrawGoodFromPermittedEvilsCollectivelyReading {Being : Type u}
    (God Evil : Being → Prop)
    (PermitsEvils CanDrawGoodFromEvils : Being → (Being → Prop) → Prop) : Prop :=
  ∀ g, God g → PermitsEvils g Evil → (∃ x, Evil x) →
    CanDrawGoodFromEvils g Evil

end TruthCore.Latin.Aquinas.SummaTheologiae
