import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaMaximumSchema
import TruthCore.Logic.ExcludedMiddle

/-! A conditional fork on the existing homogeneous-scale contrast reading.
Maximality alone is weaker than strict greatestness. The causal genus and
unrestricted cause-more-such commitments make a maximal being strictly greater
than every distinct being; neither commitment is established here. In
particular, the unrestricted causal comparative remains an explicit stronger
open reading, not a new attribution of Metaphysics II.1.

The alternative extends strict degree comparisons, not causal edges. Its
inhabitedness is supplied separately in the fork, so an empty carrier does not
serve as the intended unbounded rival. No result identifies these respects or
the strict top with God, nor denies self-causation. -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

/-- A selected maximum in being strictly exceeds every distinct being, causes
being in every distinct being, and has no distinct cause of its being. Every
maximum in being equals it. Incoming self-causation is deliberately outside
this predicate; the conclusion is not absolute uncausedness. -/
def QuartaViaStrictCausalTop {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧
    (∀ x, x ≠ m → MoreIn esse m x) ∧
    (∀ x, x ≠ m → CausesIn m x esse) ∧
    (∀ c, c ≠ m → ¬ CausesIn c m esse) ∧
    ∀ n, IsMaximumIn InAct MoreIn esse n → n = m

/-- Every being has a strictly higher being in the selected respect. This does
not assert that it has a cause, causal predecessor or infinite causal chain.
The predicate alone is vacuous on an empty carrier; the fork adds population. -/
def QuartaViaUnboundedDegrees {Being Respect : Type}
    (MoreIn : Respect → Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ x, ∃ y, MoreIn esse y x

/-- The selected perfection is instantiated, and either a strict causal top
exists or every being has a strictly higher being. This states coverage only;
horn incompatibility is a separate theorem under the same scale reading. -/
def QuartaViaDegreeFork {Being Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  (∃ x, InAct x esse) ∧
    (QuartaViaStrictCausalTop InAct MoreIn CausesIn esse ∨
      QuartaViaUnboundedDegrees MoreIn esse)

end TruthCore.Latin.Aquinas.SummaTheologiae
