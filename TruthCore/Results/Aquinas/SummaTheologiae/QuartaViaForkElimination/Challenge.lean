import TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaDegreeFork.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaUnboundedCore.Solution
import TruthCore.Models.QuartaViaDegreeFork

namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaForkElimination
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Models.QuartaViaDegreeFork

/-- Under the fork's background on the stipulated homogeneous scale, adding the
grades-to-maximum principle selects the strict causal top: `coverage` gives the
fork and `incompatible` excludes its unbounded horn. No premise is established,
and being, truth and God are not identified. -/
theorem strictTop {Being Respect : Type} [Preorder Being]
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse bonum verum nobile : Respect)
    (hScale : HomogeneousScaleReading InAct MoreIn esse)
    (hGenus : MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    QuartaViaStrictCausalTop InAct MoreIn CausesIn esse := by
  sorry

/-- The enlarged background has the existing finite Boolean witness, with the
strict top in that same interpretation; the Nat witness of the unbounded horn
satisfies the fork's background and violates the added principle. -/
theorem survivors :
    FiniteTop.JointWitness ∧
    GradesByApproachToAMaximumReading FiniteTop.model.InAct FiniteTop.model.MoreIn ∧
    Unbounded.JointWitness ∧
    ¬ GradesByApproachToAMaximumReading Unbounded.inAct Unbounded.moreIn := by
  sorry

end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaForkElimination
