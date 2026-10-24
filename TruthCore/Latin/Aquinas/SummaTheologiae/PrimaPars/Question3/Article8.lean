import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.8 co.
(*utrum Deus in compositionem aliorum veniat*), third reason.

Vocabulary as in q.3 a.7 (`ComponentOf p x`: `p` is one of the things `x` is
composed of, a part, its matter or its form) and the *quarta via*
(`IsMaximumIn InAct MoreIn esse m`: `m` has being and nothing is more a being
than it).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A8`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- No part of a composite can be simply first among beings (*nulla pars
compositi potest esse simpliciter prima in entibus*). Neither matter nor form
can: matter is in potency, which is posterior to act, and a form that is part of
a composite is participated, so posterior to what is such by essence. Aquinas
concludes, since God is *primum ens simpliciter*, that God cannot enter into the
composition of anything.

"Simply first among beings" is read as maximal in being, the *quarta via*'s
*maxime ens* (*quod est maxime ens*), to which a.8's *ostensum est* refers back.
That identification is the interpretive step of this reading. The first two
reasons (from God as first efficient cause) are not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.8 co., third reason.
-/
def NoComponentIsMaximalInBeingReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ p x, ComponentOf p x → ¬ IsMaximumIn InAct MoreIn esse p

end TruthCore.Latin.Aquinas.SummaTheologiae
