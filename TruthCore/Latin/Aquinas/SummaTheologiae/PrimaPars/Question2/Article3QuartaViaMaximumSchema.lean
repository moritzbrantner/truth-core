import TruthCore.Logic.MaximumOrder
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder

/-! Conditional instances of the maximum schema, composing the order lemmas
from #386. No new source reading is attributed here. Being, goodness and truth
remain separate respects; neither their scales nor their maxima are identified.
The unrestricted cause-more-such condition remains an explicit hypothesis,
including its open extension beyond synonymous causes (Metaphysics II.1). -/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Logic.MaximumOrder
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- Realize the schema at the chosen perfection. The semantic relation is
`CausesIn c x r`; no generic `depends` relation replaces it. -/
def perfectionOrderSystem {Being Respect : Type}
    (CausesIn : Being → Being → Respect → Prop) (r : Respect) : System Being :=
  ⟨fun c x => CausesIn c x r⟩

/-- The source-shaped causal comparative becomes the schema's strict ascent
only after the homogeneous-scale representation is supplied. -/
theorem HomogeneousScaleReading.causesRaiseDegree {Being Respect : Type}
    [Preorder Being] {InAct : Being → Respect → Prop}
    {MoreIn : Respect → Being → Being → Prop}
    {CausesIn : Being → Being → Respect → Prop} {r : Respect}
    (h : HomogeneousScaleReading InAct MoreIn r)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn) :
    (perfectionOrderSystem CausesIn r).CausesRaiseDegree :=
  fun c x hne hc => (h.2 c x).mp (hCause c x r hne hc)

/-- One conditional instance family, explicitly covering being, goodness and
truth. For each named respect, a homogeneous scale plus the unrestricted
cause-more-such premise implies that a maximum has no distinct cause of that
same perfection. Nothing says a maximum exists or that these maxima coincide. -/
def FourthWayMaximumSchemaInstances : Prop :=
  ∀ (Being Respect : Type) [Preorder Being]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse bonum verum : Respect),
    CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
    ∀ r, (r = esse ∨ r = bonum ∨ r = verum) →
      HomogeneousScaleReading InAct MoreIn r →
      ∀ m, IsMaximumIn InAct MoreIn r m →
        ∀ c, c ≠ m → ¬ CausesIn c m r

/-- Attribution is an instance via the exact preorder pulled back from degrees
of approach (#386 `homogeneousLift`). Universal possession is additional:
`ApproachToPrimaryReading` supplies possession only for the primary. Strict
primacy, the creature bridge, and the primary's causal clause are not used.
The cause-more-such condition is still required and can fail for secondary
causes in the existing attribution countermodel. -/
def AttributionMaximumSchemaInstance : Prop :=
  ∀ (Being Respect Degree : Type) [Preorder Degree]
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (r : Respect) (near : Being → Degree) (p : Being),
    ApproachToPrimaryReading InAct MoreIn r near p →
    (∀ x, InAct x r) →
    CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn →
    ∀ m, IsMaximumIn InAct MoreIn r m → ∀ c, c ≠ m → ¬ CausesIn c m r

end TruthCore.Latin.Aquinas.SummaTheologiae
