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

/-- God permits evil only so as to bring good out of it: God, being supremely
good, "would in no way allow any evil in his works unless he were so
omnipotent and good as to bring good even out of evil"; "it belongs to the
infinite goodness of God that he permit evils to be, and draw goods from them"
(*ut esse permittat mala, et ex eis eliciat bona*).

Read per evil: for every evil there is, God brings out of it some good,
namely some being's having a perfection (goodness is being in act, I q.5 a.1).
A weaker reading (God draws good from the evils taken together) is possible;
the per-evil reading is the stronger commitment, so a consistency result proved
with it also holds for the weaker one. The reading does not say that the good
outweighs the evil, nor that it goes to the one who suffers the evil.

Source: Thomas Aquinas, *Summa theologiae* I q.2 a.3 ad 1.
-/
def GodDrawsGoodFromEveryEvilReading {Being : Sort u} {Perfection : Sort v}
    (God Evil : Being → Prop) (GoodIn : Being → Perfection → Prop)
    (DrawsGoodFrom : Being → Being → Being → Perfection → Prop) : Prop :=
  ∀ g x, God g → Evil x → ∃ y p, GoodIn y p ∧ DrawsGoodFrom g x y p

end TruthCore.Latin.Aquinas.SummaTheologiae
