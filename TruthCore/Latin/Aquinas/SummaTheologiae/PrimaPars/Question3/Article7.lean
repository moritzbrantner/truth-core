import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.3 a.7 co.
(*utrum Deus sit omnino simplex*).

* `Composite x` — `x` is composed in any way at all.
* `ComponentOf p x` — `p` is one of the things `x` is composed of (a part, its
  matter or form, its essence or esse). Components are quantified over the same
  `Being` domain, so that the priority relation `PriorSimply` of q.3 a.1 applies
  to them.
* `ComposedOfMatterAndForm x` — `x` is composed of matter and form (q.3 a.2).
* `essenceOf x`, `esseOf x : Principle` — the essence of `x` and its act of
  being (q.3 a.4).

Formalized: the inclusion of matter-form and essence-esse composition among
compositions (from the first proof), the second proof (a composite is posterior
to its components) and the premise of the fifth (every composite has something
in it that is not itself). The first proof's exhaustive enumeration, the third
and fourth proofs, and the second half of the fifth are not formalized.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q3-A7`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u w

/-- Composition of matter and form, and an esse other than the essence, are kinds
of composition (*neque compositio formae et materiae ... neque aliud essentia et
esse ... manifestum est quod Deus nullo modo compositus est*).

Only the inclusion is used: whatever is composed of matter and form, or has an
esse other than its essence, is composite. The first proof's other claim, that
the listed kinds exhaust composition, is not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., first proof.
-/
def MatterFormAndEsseEssenceAreCompositionsReading {Being : Sort u}
    {Principle : Sort w}
    (ComposedOfMatterAndForm Composite : Being → Prop)
    (essenceOf esseOf : Being → Principle) : Prop :=
  ∀ x, (ComposedOfMatterAndForm x → Composite x) ∧
    (esseOf x ≠ essenceOf x → Composite x)

/-- Every composite is posterior to its components and depends on them (*omne
compositum est posterius suis componentibus, et dependens ex eis*).

Read with the simple priority of q.3 a.1: each component of `x` is simply prior
to `x`.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., second proof.
-/
def CompositePosteriorToComponentsReading {Being : Sort u}
    (ComponentOf PriorSimply : Being → Being → Prop) : Prop :=
  ∀ p x, ComponentOf p x → PriorSimply p x

/-- In every composite there is something that is not itself (*Sic igitur in omni
composito est aliquid quod non est ipsum*): every composite has a component other
than itself.

Source: Thomas Aquinas, *Summa theologiae* I q.3 a.7 co., fifth proof.
-/
def CompositeHasComponentOtherThanItselfReading {Being : Sort u}
    (Composite : Being → Prop) (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ x, Composite x → ∃ p, ComponentOf p x ∧ p ≠ x

end TruthCore.Latin.Aquinas.SummaTheologiae
