/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.7 co.
(*utrum Deus sit omnino simplex*), third proof, used for stage 2 (#143).

Vocabulary as in q.3 a.7 (`Composite x`) and the *quarta via* (`CausesIn c x esse`:
`c` causes the being of `x`).

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A7`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Every composite has a cause (*omne compositum causam habet*): things diverse
in themselves do not come together into one except through some cause uniting
them (*nisi per aliquam causam adunantem ipsa*).

The uniting cause is read as a cause, other than the composite, of its being:
a composite is, as this one thing, only by being united. That is the interpretive
step of this reading. Aquinas concludes that God, who has no cause since he is
the first efficient cause, is not composite.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., third proof.
-/
def CompositeHasAUnitingCauseReading {Being : Sort u} {Respect : Sort v}
    (Composite : Being → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) : Prop :=
  ∀ x, Composite x → ∃ c, c ≠ x ∧ CausesIn c x esse

end TruthCore.Latin.Aquinas.SummaTheologiae
