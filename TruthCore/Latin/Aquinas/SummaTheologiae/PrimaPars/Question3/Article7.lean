import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.3 a.7 co.
(*utrum Deus sit omnino simplex*).

* `Composite x` — `x` is composed in any way at all (of parts, of matter and
  form, of essence and esse, …).

Only the fourth proof of the *respondeo* is formalized (every composite has
potency and act). The first proof gathers the exclusions of q.3 a.1–a.6 and
needs a.3, a.5 and a.6; the second and third rest on God having no cause (the
second way); the fifth rests on God being form or esse itself.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A7`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- In every composite there must be potency and act (*in omni composito oportet
esse potentiam et actum ... quia vel una partium est actus respectu alterius;
vel saltem omnes partes sunt sicut in potentia respectu totius*).

Whatever is composite is in potency in some respect. As in q.3 a.4, the potency
may belong to a part of `x`; only its existence is used.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., fourth proof.
-/
def CompositeIsInPotencyReading {Being : Sort u} {Respect : Sort v}
    (InPotency : Being → Respect → Prop)
    (Composite : Being → Prop) : Prop :=
  ∀ x, Composite x → ∃ r, InPotency x r

end TruthCore.Latin.Aquinas.SummaTheologiae
