import TruthCore.Causality.CogitoNecessaryConcrete

namespace TruthCore.Results.Causality.CogitoNecessaryConcrete

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

/-- Thinker-local fork: an occurring thought with a concrete bearer existing at
`w`, accessible for actual concrete grounding, has either a necessary concrete
ground-ancestor or a contingent concrete root among its ground-ancestors. -/
theorem ancestryRootFork {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    ThinkerAncestryRootFork m Occurs Bears w := by
  sorry

/-- Adding the thinker-local anti-brute-root principle closes the second horn:
some bearer of an occurring thought has a necessary concrete ground-ancestor. -/
theorem necessaryConcreteAncestor {W B Episode : Type}
    (m : Profile W B) (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteAncestorOfThinker m Occurs Bears w := by
  sorry

/-- The global premises imply the local ones but not conversely, and each
non-logical premise of `necessaryConcreteAncestor` is needed. -/
theorem ancestryControls : CogitoAncestryControls := by
  sorry

end TruthCore.Results.Causality.CogitoNecessaryConcrete
