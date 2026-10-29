import TruthCore.Causality.OccurrenceUnderivedEssence
namespace TruthCore.Results.Causality.OccurrenceUnderivedEssence
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.OccurrenceUnderivedEssence
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Refine the existing #564 descent without dropping its root property;
transport actual support into that SAME grounding relation, and apply the
existing #680 q3 theorem to that SAME individual. No necessity→underived step. -/
theorem checks {W B Episode P A : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hSupport : ActualSupportIsConcreteGround m R w)
    (hInAct : ExistingInActAt m.ontic p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m.ontic p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m.ontic R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    SameWitnessEssenceIdentity m Occurs Bears R w p := by
  sorry

theorem recipient_control : NecessaryRecipientControl := by
  sorry
end TruthCore.Results.Causality.OccurrenceUnderivedEssence
