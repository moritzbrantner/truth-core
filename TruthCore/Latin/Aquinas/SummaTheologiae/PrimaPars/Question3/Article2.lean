import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.2 co.
(*utrum in Deo sit compositio formae et materiae*).

* `ComposedOfMatterAndForm x` — `x` is composed of matter and form.

Only the first proof of the *respondeo* is formalized (from pure act). The
second (from goodness by participation) and third (the first agent is form by
its essence) are not.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A2`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Matter is that which is in potency (*materia est id quod est in potentia*):
whatever is composed of matter and form is in potency in some respect.

Aquinas speaks of matter, a principle of the composite. The reading attributes
the potency to the composite, in an unspecified respect; that is all the
argument uses.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.2 co., first proof.
-/
def MatterIsInPotencyReading {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop)
    (ComposedOfMatterAndForm : Being → Prop) : Prop :=
  ∀ x, ComposedOfMatterAndForm x → ∃ r, InPotency x r

end TruthCore.Latin.Aquinas.SummaTheologiae
