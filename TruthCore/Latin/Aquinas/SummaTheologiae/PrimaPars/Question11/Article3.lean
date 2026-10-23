import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.11 a.3 co.
(*utrum Deus sit unus*).

`InAct f r` is read here as "`f` has the perfection `r`", formally or
eminently. That is the same abstract predicate as in the *prima via*, where the
mover's being in act may be virtual.

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

/-- Things that are many must differ: something belongs to one that does not
belong to the other (*Si ergo essent plures dii, oporteret eos differre.
Aliquid ergo conveniret uni, quod non alteri*).

Stated in the contrapositive, which is classically equivalent and lets the
uniqueness conclusion be a plain equality without axioms: beings that agree in
every act (what belongs to one in act belongs to the other, and conversely) are
not many but one.

Read as a general principle about any two beings, with "what belongs" read as
being in act in a respect. That is stronger than the plural-gods case needs: it
is an identity of indiscernibles over acts, open to the objection that two
material individuals may differ only in matter. A version restricted to totally
perfect beings would be equivalent to the conclusion and so would make the
argument a transcription.

Source: Thomas Aquinas, *Summa theologiae* I q.11 a.3 co., second proof.
-/
def ManyMustDifferReading {Being : Sort u} {Respect : Sort v}
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ x y, (∀ r, (InAct x r → InAct y r) ∧ (InAct y r → InAct x r)) → x = y

/-- The first mover comprehends in itself the whole perfection of being
(*Ostensum est enim supra quod Deus comprehendit in se totam perfectionem
essendi*): every first mover moved by none is in act in every respect.

Aquinas cites this as shown (in q.4 a.2). Applied to the *prima via*'s mover it
is an open premise: neither the *prima via* nor q.3 entails it, and q.4 a.2's
argument (the perfections of effects pre-exist in the first efficient cause)
rests on the second way. With `NotActAndPotencyInSameRespectReading` it would
also yield pure act.

Source: Thomas Aquinas, *Summa theologiae* I q.11 a.3 co., second proof.
-/
def FirstUnmovedMoverHasEveryPerfectionReading {Being : Sort u} {Respect : Sort v}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop) : Prop :=
  ∀ f, ((∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r) → ∀ r, InAct f r

end TruthCore.Latin.Aquinas.SummaTheologiae
