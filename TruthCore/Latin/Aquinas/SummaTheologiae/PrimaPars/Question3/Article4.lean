import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.4 co.
(*utrum in Deo sit idem essentia et esse*).

* `Principle` — metaphysical principles of a being, such as its essence and its
  act of being.
* `essenceOf x`, `esseOf x` — the essence (*essentia*, *natura*) of `x` and its
  act of being (*esse*).

Only the second proof of the *respondeo* is formalized (esse is the actuality of
every form or nature). The first and third proofs rest on God being the first
efficient cause (the second way) and on q.3 a.3 (God is his essence), which this
corpus has not formalized.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A4`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- Esse is the actuality of every form or nature, so an essence other than its
esse is related to it as potency to act (*esse est actualitas omnis formae vel
naturae ... Oportet igitur quod ipsum esse comparetur ad essentiam quae est
aliud ab ipso, sicut actus ad potentiam*).

Whatever has an esse other than its essence is in potency in some respect.
Aquinas places the potency in the essence, a principle of the thing, so this
reading needs `InPotency x r` to cover a potency *in* `x`. q.3 a.4 itself
concludes from *in Deo nihil sit potentiale*, which is this broad sense.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.4 co., second proof.
-/
def EsseOtherThanEssenceIsPotencyReading {Being : Sort u} {Respect : Sort v}
    {Principle : Sort w}
    (InPotency : Being → Respect → Prop)
    (essenceOf esseOf : Being → Principle) : Prop :=
  ∀ x, esseOf x ≠ essenceOf x → ∃ r, InPotency x r

end TruthCore.Latin.Aquinas.SummaTheologiae
