import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.7 a.1 co.
(*utrum Deus sit infinitus*) and I q.10 a.1-2 co. (*quid sit aeternitas*;
*utrum Deus sit aeternus*), used for stage 2, group 2 (#143).

Vocabulary: `essenceOf x`, `esseOf x` as in q.3 a.4 and a.7; `InPotency x r` and
`PureAct` as in the *prima via* and q.3 a.1; `Infinite x` and `Eternal x` are
primitive predicates whose content these readings constrain.

Source witnesses: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passages `AQUINAS-ST-I-Q7-A1`, `AQUINAS-ST-I-Q10-A1` and
`AQUINAS-ST-I-Q10-A2`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- What is its own subsistent being is infinite: form not received in matter has
infinity in the sense of perfection, and "what is most formal of all is being
itself"; since the divine being is "not received in anything, but he is his own
subsistent being", God is infinite and perfect.

"Not received in anything" is read through q.3 a.4 as the identity of essence
and act of being: a being whose esse is its essence is infinite.

Source: Thomas Aquinas, *Summa theologiae* I q.7 a.1 co.
-/
def SubsistentBeingIsInfiniteReading {Being : Sort u} {Principle : Sort w}
    (essenceOf esseOf : Being → Principle) (Infinite : Being → Prop) : Prop :=
  ∀ x, esseOf x = essenceOf x → Infinite x

/-- What is altogether immutable is eternal: "the notion of eternity follows
immutability, as the notion of time follows movement" (a.2), and what is
altogether immutable "can have no succession, nor beginning nor end" (a.1), the
two marks of eternity.

Altogether immutable is read as in potency in no respect (pure act): not only
not changing now, but without any capacity for change (q.9 a.1: whatever is
changed in any way is in some way in potency). Codex P1 on #199: "moved in no
respect" in the *prima via*'s present-tense sense would be too weak.

Source: Thomas Aquinas, *Summa theologiae* I q.10 a.2 co., with a.1 co.
-/
def ImmutableIsEternalReading {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop) (Eternal : Being → Prop) : Prop :=
  ∀ x, PureAct InPotency x → Eternal x

end TruthCore.Latin.Aquinas.SummaTheologiae
