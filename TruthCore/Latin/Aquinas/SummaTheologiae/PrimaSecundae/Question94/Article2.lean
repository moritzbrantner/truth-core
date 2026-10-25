/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I-II q.94 a.2 co.
(*utrum lex naturalis contineat plura praecepta, vel unum tantum*), used by the
Catholic natural-law theory of #185.

Vocabulary, all of it parameters rather than definitions:

* `Act` — what can be done or pursued.
* `Good a`, `Evil a` — `a` is good, evil.
* `ToBePursued a`, `ToBeAvoided a` — `a` is to be done and pursued, to be
  avoided.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 7 (Rome 1892),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-II-Q94-A2`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u

/-- The first precept of the natural law: good is to be done and pursued, and
evil avoided (*hoc est ergo primum praeceptum legis, quod bonum est faciendum et
prosequendum, et malum vitandum*). It is founded on the notion of the good
(*bonum est quod omnia appetunt*), and all the other precepts of the natural
law are founded on it.

Formalized as two universal conditionals. The precept's self-evidence (*per se
nota*) is a separate claim about its epistemic status, not part of this
proposition.

Source: Aquinas, *Summa theologiae* I-II q.94 a.2 co.
-/
def FirstPreceptOfNaturalLawReading {Act : Sort u}
    (Good Evil ToBePursued ToBeAvoided : Act → Prop) : Prop :=
  (∀ a, Good a → ToBePursued a) ∧ (∀ a, Evil a → ToBeAvoided a)

end TruthCore.Latin.Aquinas.SummaTheologiae
