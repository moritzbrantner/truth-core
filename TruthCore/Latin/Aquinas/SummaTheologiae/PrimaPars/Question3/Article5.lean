import TruthCore.Greek.Aristotle.MetaphysicsIII3

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.3 a.5 co.
(*utrum Deus sit in genere aliquo*), the second of the three proofs that God
is not in a genus as a species (issue #340).

Aquinas distinguishes two ways of being in a genus: *simpliciter et proprie,
sicut species, quae sub genere continentur*, and *per reductionem, sicut
principia et privationes* (the point is reduced to quantity). Only the first is
formalized here: `InGenus x g` says that `x` is in the genus `g` as a species
or member contained under it. Being in a genus by reduction, the first and the
third proofs, and the closing argument that God is not in a genus even as a
principle are not formalized.

The second proof reuses Aristotle's predication vocabulary from
`TruthCore.Greek.Aristotle.MetaphysicsIII3` (`IsGenus`, `DifferentiaOf`,
`SaidOf`, `ens`) and adds:

* `Being` — the things that are in genera (here: God and creatures);
* `InGenus : Being → Term → Prop` — `x` is in the genus `g` *simpliciter et
  proprie*;
* `IsGod : Being → Prop` — `x` is God (`DEF-GOD-OF-CLASSICAL-THEISM`; nothing
  here defines it).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A5`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- What is in a genus properly is contained under a genus (*Uno modo,
simpliciter et proprie; sicut species, quae sub genere continentur*): whatever
`x` is in as in a genus is a genus in the strict sense.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.5 co. -/
def InGenusOnlyUnderAGenusReading {Being : Sort u} {Term : Sort v}
    (IsGenus : Term → Prop) (InGenus : Being → Term → Prop) : Prop :=
  ∀ x g, InGenus x g → IsGenus g

/-- If God were in a genus, his genus would be being (*cum esse Dei sit eius
essentia, ut ostensum est, si Deus esset in aliquo genere, oporteret quod genus
eius esset ens: nam genus significat essentiam rei, cum praedicetur in eo quod
quid est*).

Stated, as in the sentence, for God. The reasons Aquinas gives (God's esse is
his essence, q.3 a.4; a genus signifies the essence of the thing, being said of
it in what it is) are carried by this conditional and are not formalized
separately; in particular the premise is not stated for every being whose esse
is its essence.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.5 co., second proof. -/
def GenusOfGodWouldBeBeingReading {Being : Sort u} {Term : Sort v}
    (IsGod : Being → Prop) (InGenus : Being → Term → Prop) (ens : Term) :
    Prop :=
  ∀ x g, IsGod x → InGenus x g → g = ens

/-- God is in no genus (*Unde relinquitur quod Deus non sit in genere*): no God
is in any genus *simpliciter et proprie*.

Only the strict way of being in a genus is concluded. Not being in a genus *per
reductionem* is a separate conclusion of the same article and is not
formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.5 co., second proof. -/
def GodIsInNoGenusReading {Being : Sort u} {Term : Sort v}
    (IsGod : Being → Prop) (InGenus : Being → Term → Prop) : Prop :=
  ∀ x g, IsGod x → ¬ InGenus x g

end TruthCore.Latin.Aquinas.SummaTheologiae
