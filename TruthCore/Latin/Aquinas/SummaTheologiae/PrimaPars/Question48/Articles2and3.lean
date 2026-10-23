/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.48 a.2
(*utrum malum inveniatur in rebus*) and a.3 (*utrum malum sit in bono sicut in
subiecto*).

Vocabulary, all of it parameters rather than definitions:

* `Being`, `Perfection`, `Has x p` — as in I q.5 a.1.
* `Due x p` — `p` is a good due to `x`: `x` is by nature apt to have it (so a
  man lacking sight lacks a due good; a man lacking a lion's strength does not).
* `Evil x` — there is evil in `x`.
* `Sentence`, `Holds φ`, `evilPremise` — sentences, truth, and the sentence
  "there is evil (in the world)".

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passages `AQUINAS-ST-I-Q48-A2` and `AQUINAS-ST-I-Q48-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- Evil is the privative removal of good: not every lack of good is evil, but
only the lack of a good the subject is apt to have
(*remotio boni negative accepta, mali rationem non habet ... sed remotio boni
privative accepta, malum dicitur: sicut privatio visus caecitas dicitur*).

Both directions are in the text: privative removal "is called evil", and
negative removal "does not have the nature of evil". The reading does not
formalize that the subject of the privation is a being in potency.

Source: Thomas Aquinas, *Summa theologiae* I q.48 a.3 co.
-/
def EvilIsPrivationReading {Being : Sort u} {Perfection : Sort v}
    (Evil : Being → Prop) (Due Has : Being → Perfection → Prop) : Prop :=
  ∀ x, Evil x ↔ ∃ p, Due x p ∧ ¬ Has x p

/-- Some things fall short of good: the perfection of the universe requires
things that can fail from goodness, "whence it follows that they sometimes
fail" (*ad quod sequitur ea interdum deficere*); and the nature of evil
consists in this, that something fails from good (*in hoc autem consistit
ratio mali, ut scilicet aliquid deficiat a bono*).

Only the fact of deficiency is formalized, in non-evaluative vocabulary: some
being lacks a good due to it. The explanation from the order of the universe is
not part of the reading. That this deficiency *is* evil follows only with
`EvilIsPrivationReading`.

Source: Thomas Aquinas, *Summa theologiae* I q.48 a.2 co.
-/
def SomethingFallsShortOfDueGoodReading {Being : Sort u} {Perfection : Sort v}
    (Due Has : Being → Perfection → Prop) : Prop :=
  ∃ x p, Due x p ∧ ¬ Has x p

/-- Evil "is" in the sense in which *being* signifies the truth of a proposition,
the sense that answers the question *an est*: as we say blindness is in the eye
(*alio modo dicitur ens, quod significat veritatem propositionis ... et hoc
modo etiam malum dicitur ens*).

Read as: if there is evil in something, the sentence "there is evil" is true.
Only this direction is formalized. It makes explicit that, on this account,
the evil premise is a truth-apt proposition whose truth is fixed by a
privation in a subject, not by anyone's attitude.

Source: Thomas Aquinas, *Summa theologiae* I q.48 a.2 ad 2.
-/
def EvilIsAsPropositionalTruthReading {Being : Sort u} {Sentence : Sort w}
    (Evil : Being → Prop) (Holds : Sentence → Prop) (evilPremise : Sentence) : Prop :=
  (∃ x, Evil x) → Holds evilPremise

end TruthCore.Latin.Aquinas.SummaTheologiae
