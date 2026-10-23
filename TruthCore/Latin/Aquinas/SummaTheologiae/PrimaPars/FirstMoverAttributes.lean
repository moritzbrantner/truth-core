import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article2
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7

/-!
The simplicity conclusions of ST I q.3 a.1, a.2, a.4 and a.7, gathered for the
*prima via*'s first mover. Each conjunct is a conclusion Aquinas states in one
of those articles about God, read as being about the first mover moved by none
(q.3 a.1 co.: *Ostensum est autem supra quod Deus est primum movens immobile*).
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v w

/-- Every first mover moved by none is not a body (q.3 a.1 co., first proof:
*Deus non est corpus*), not composed of matter and form (q.3 a.2 co.: *impossibile
est quod Deus sit compositus ex materia et forma*), has no esse other than its
essence (q.3 a.4 co.: *sua igitur essentia est suum esse*), and is not composite
in any way (q.3 a.7 co.: *Deus nullo modo compositus est, sed est omnino
simplex*).

The essence-esse identity is stated as "not distinct", which is classically
the same and keeps the result axiom-free. -/
def FirstUnmovedMoverIsSimpleReading {Being : Sort u} {Respect : Sort v}
    {Principle : Sort w}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (Body ComposedOfMatterAndForm Composite : Being → Prop)
    (essenceOf esseOf : Being → Principle) : Prop :=
  ∀ f, ((∃ x r, MovesIn f x r) ∧ ∀ r, ¬ MovedIn f r) →
    ¬ Body f ∧ ¬ ComposedOfMatterAndForm f ∧ ¬ esseOf f ≠ essenceOf f ∧ ¬ Composite f

end TruthCore.Latin.Aquinas.SummaTheologiae
