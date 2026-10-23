import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.11 a.3 co.
(*utrum Deus sit unus*).

`InAct f r` is read here as "`f` has the perfection `r`", formally or
eminently. That is the same abstract predicate as in the *prima via*, where the
mover's being in act may be virtual.

The other premise of the second proof, *Ostensum est enim supra quod Deus
comprehendit in se totam perfectionem essendi*, is a back-reference to q.4 a.2
about God. It is not read here as a claim about every first mover moved by none;
that step is the unsourced open bridge
`TruthCore.Case.Catholicism.FirstUnmovedMoverHasEveryPerfection`.

The conclusion, *impossibile est ergo esse plures Deos*, is
`TruthCore.Case.Catholicism.AtMostOneFirstUnmovedMover` (#159).

Only the second proof (from the infinity of God's perfection) is formalized. The
first (God is his own nature) needs q.3 a.3. The third (from the unity of the
world's order) needs the fifth way.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q11-A3`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- If there were several first movers moved by none, they would have to differ:
something would belong to one that does not belong to the other (*Si ergo essent
plures dii, oporteret eos differre. Aliquid ergo conveniret uni, quod non
alteri*).

Scoped to the plural hypothesis of the argument, the weakest reading that the
argument uses: two distinct first movers moved by none differ in some act, one
being in act in a respect in which the other is not. "What belongs" is read as
being in act in a respect. Whether the differing item is a perfection or a
privation (*si hoc esset privatio ... si autem hoc esset perfectio*) is the
choice of which of the two is in act; both horns are the same disjunction here.
The premise does not say that the first movers are perfect, so it does not
entail the conclusion on its own: a model with two first movers that differ in
some act satisfies it.

Source: Thomas Aquinas, *Summa theologiae* I q.11 a.3 co., second proof.
-/
def PluralFirstMoversWouldDifferInActReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ f g, ((∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r) →
    ((∃ x r, MovesIn g x r) ∧ ∀ r, ¬ MovedIn g r) → f ≠ g →
    ∃ r, (InAct f r ∧ ¬ InAct g r) ∨ (InAct g r ∧ ¬ InAct f r)

end TruthCore.Latin.Aquinas.SummaTheologiae
