/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.4 a.1
(*utrum Deus sit perfectus*), reply to the third objection.

Vocabulary as in the *prima via* (`Question2.Article3`) and the *quarta via*
(`Question2.Article3QuartaVia`): `InAct x r` says that `x` is in act in the
respect (has the perfection) `r`, and `esse` is the respect of being.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q4-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Nothing has actuality except insofar as it is (*Nihil enim habet actualitatem,
nisi inquantum est: unde ipsum esse est actualitas omnium rerum, et etiam
ipsarum formarum*).

Whatever is in act in some respect has being. Only this consequence is
formalized, not the thesis that *esse* is the most perfect of all and related to
everything as act.

Source: Thomas Aquinas, *Summa theologiae* I q.4 a.1 ad 3.
-/
def ActualityOnlyInsofarAsBeingReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ x r, InAct x r → InAct x esse

end TruthCore.Latin.Aquinas.SummaTheologiae
