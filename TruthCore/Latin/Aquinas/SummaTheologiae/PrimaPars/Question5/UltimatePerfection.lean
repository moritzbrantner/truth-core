/-! A bounded reading of ST I q.5 a.1 ad 1, in the same materialized pinned
article as the existing per-perfection actuality reading. This sibling records
the distinction its doc comment explicitly leaves outside that reading. -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

/-- If a thing lacks the ultimate perfection it ought to have, it is not good
simpliciter, even though it has some perfection insofar as it is actual.
Only the exclusion clause is encoded: no occurrence of such a deficient thing
is asserted. `UltimateDuePerfection` is a primitive condition, not every
actual perfection or a definition of categorical moral authority. The negative
form follows the cited clause without silently applying classical contraposition.
Source: ST I q.5 a.1 ad 1, "Quod autem non habet ultimam perfectionem quam debet
habere ... nec bonum simpliciter, sed secundum quid."
-/
def UltimateDuePerfectionRequiredReading {Being : Sort u}
    (GoodSimply UltimateDuePerfection : Being → Prop) : Prop :=
  ∀ x, ¬ UltimateDuePerfection x → ¬ GoodSimply x

end TruthCore.Latin.Aquinas.SummaTheologiae
