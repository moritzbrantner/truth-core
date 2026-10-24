import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.8 co.
(*utrum Deus in compositionem aliorum veniat*), third reason.

Vocabulary as in q.3 a.7 (`ComponentOf p x`: `p` is one of the things `x` is
composed of, a part, its matter or its form) and q.3 a.1 (`IsFirstBeing
PriorSimply f`: no being other than `f` is simply prior to it).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A8`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u

/-- No part of a composite can be simply first among beings (*nulla pars
compositi potest esse simpliciter prima in entibus*). Neither matter nor form
can: matter is in potency, which is posterior to act, and a form that is part of
a composite is participated, so posterior to what is such by essence. Aquinas
concludes, since God is *primum ens simpliciter*, that God cannot enter into the
composition of anything.

"Simply first among beings" is read with q.3 a.1's notion of the first being
(nothing other is simply prior to it), the notion the third reason itself uses:
components are excluded because something is prior to them. The first two
reasons (from God as first efficient cause) are not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.8 co., third reason.
-/
def NoComponentIsFirstBeingReading {Being : Sort u}
    (ComponentOf PriorSimply : Being → Being → Prop) : Prop :=
  ∀ p x, ComponentOf p x → ¬ IsFirstBeing PriorSimply p

end TruthCore.Latin.Aquinas.SummaTheologiae
