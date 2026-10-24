/-!
The temporal quantifier shift behind the *tertia via*'s contested step (#146).

`EachSometimeNotEntailsSometimeNothing` is the naive principle: whenever each
thing is, at some time, not, there is a time at which nothing is
(`∀x ∃t ¬E x t ⊢ ∃t ∀x ¬E x t`). It is invalid; result
`LOGIC-QUANTIFIER-SHIFT-EACH-SOMETIME-NOT-INVALID` gives a two-being, two-time
countermodel.
-/

namespace TruthCore.Logic

/-- The naive quantifier shift as a logical principle: in every domain of beings
and times, if each being is at some time not, then at some time no being is. -/
def EachSometimeNotEntailsSometimeNothing : Prop :=
  ∀ (Being Time : Type) (IsAt : Being → Time → Prop),
    (∀ x, ∃ t, ¬ IsAt x t) → ∃ t, ∀ x, ¬ IsAt x t

/-- The naive quantifier shift is not a valid principle. -/
def EachSometimeNotDoesNotEntailSometimeNothing : Prop :=
  ¬ EachSometimeNotEntailsSometimeNothing

end TruthCore.Logic
