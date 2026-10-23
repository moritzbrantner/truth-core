/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
(*utrum bonum differat secundum rem ab ente*).

Vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over.
* `Perfection` — the perfections (acts) a thing can have.
* `Has x p` — `x` actually has perfection `p` (is in act in that respect).
* `GoodIn x p` — `x` is good in respect of `p`.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q5-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Good and being are the same in reality and differ only in concept
(*bonum et ens sunt idem secundum rem: sed differunt secundum rationem tantum*):
a thing is good insofar as it is a being, that is, insofar as it is in act
(*intantum est aliquid bonum, inquantum est ens*).

Formalized per perfection: `x` is good in respect of `p` exactly when it
actually has `p`. The biconditional captures only "the same in reality"
(coextension); the difference in concept (good adds the notion of the
desirable) is not formalized. The reply to the first objection's distinction
between being *simpliciter* and good *simpliciter* is not formalized either.

Source: Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
-/
def GoodnessIsActualityReading {Being : Sort u} {Perfection : Sort v}
    (GoodIn Has : Being → Perfection → Prop) : Prop :=
  ∀ x p, GoodIn x p ↔ Has x p

end TruthCore.Latin.Aquinas.SummaTheologiae
