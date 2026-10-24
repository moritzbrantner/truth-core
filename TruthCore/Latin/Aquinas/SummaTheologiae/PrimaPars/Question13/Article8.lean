import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.13 a.8
(*utrum hoc nomen Deus sit nomen naturae*), with the *quarta via*'s closing
*et hoc dicimus Deum* (q.2 a.3 co.) and q.2 a.2 ad 2 as context.

Vocabulary as in the *quarta via* (`Question2.Article3QuartaVia`: `InAct`,
`MoreIn`, `CausesIn`, `esse`) and q.105 a.5 (`God : Being → Prop`, the one the
*Summa* calls God).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q13-A8`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Nominal definition of the name "God". The name is imposed to signify something
that exists above all and is the principle of all (q.13 a.8 ad 2: *Impositum est
enim nomen hoc ad aliquid significandum supra omnia existens, quod est principium
omnium, et remotum ab omnibus. Hoc enim intendunt significare nominantes Deum*).
At the end of the *quarta via* the same name is given to what is the cause of
being of all beings (*et hoc dicimus Deum*). In proving that God exists, what the
name signifies serves as the middle term, because the names of God are imposed
from his effects (q.2 a.2 ad 2).

Formalized as a definite description. If a being `m` is maximal in being ("above
all"), causes the being of every other being ("principle of all"), and is the
only being maximal in being, then `God m`: `m` is the one the *Summa* calls God,
also in q.105 a.5.

Fidelity notes:
* The definition is nominal. It fixes what the name is used for (*quid significet
  nomen*), not what God is (*quod quid est*; q.2 a.2 ad 2). That the name "God"
  in q.2 a.3 and in q.105 a.5 is one name with one use is the content of this
  premise. It is not proved.
* The uniqueness clause reads *hoc* ("this", a single thing) and the singular
  *aliquid … quod est principium omnium* as a definite description that refers
  only when exactly one thing fits. Without that clause, the name would apply to
  every being that is maximal in being and causes the being of the others.
  q.13 a.9 adds that, by its *ratio*, the name is communicable (people can
  conceive of several gods), so the uniqueness belongs to the thing named, not to
  the name's meaning. Here it is a condition of application. It is not asserted.
* "Above all" is read as maximal in being: nothing is more a being. "Principle
  of all" is read as cause of being of every other being, which is the only one
  of the *quarta via*'s clauses that is formalized. *Remotum ab omnibus* (the way
  of negation) is not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.13 a.8 ad 2; q.2 a.3 co.
(*quarta via*); q.2 a.2 ad 2.
-/
def GodNamesTheUniqueMaximeEnsReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (God : Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m →
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m) → God m

end TruthCore.Latin.Aquinas.SummaTheologiae
