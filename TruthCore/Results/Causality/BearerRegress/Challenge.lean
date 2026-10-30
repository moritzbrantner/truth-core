import TruthCore.Causality.BearerRegress

namespace TruthCore.Results.Causality.BearerRegress

open TruthCore.Causality.BearerRegress
open TruthCore.Causality.NecessarilyUnderived (WellFoundedPresentEsseSupport)
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Greek.Aristotle.Categories (PrimarySubstanceBySubjectRelationsReading)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

/-- Coverage only: some bearer of an occurring thought has a terminus satisfying
`Substance`, a terminus failing it, a support cycle below it, or an acyclic
endless ancestry. -/
theorem someBearerOutcome {W B Episode : Type}
    (m : Ontic W B) (R : W → B → B → Prop) (Dependent Substance : B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hEM : ExcludedMiddle) :
    SomeBearerOutcome m R Dependent Substance Occurs Bears w := by
  sorry

/-- With actual support well-founded and both subject relations yielding existing
support, some bearer of an occurring thought has a terminus that passes the
*Categories* negative primary-substance test. -/
theorem primarySubstanceTerminus {W B Episode : Type}
    (m : Ontic W B) (R : W → B → B → Prop) (Dependent IsPrimarySubstance : B → Prop)
    (SaidOf In : B → B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hWF : WellFoundedPresentEsseSupport m R w)
    (hReading : PrimarySubstanceBySubjectRelationsReading IsPrimarySubstance SaidOf In)
    (hIn : InSubjectIsExistentSupport m R In w)
    (hSaidOf : SaidOfSubjectIsExistentSupport m R SaidOf w)
    (hEM : ExcludedMiddle) :
    PrimarySubstanceTerminusOfBearer m R Dependent IsPrimarySubstance Occurs Bears w := by
  sorry

/-- The branch witnesses, omission models and exclusions. -/
theorem controls : BearerRegressControls := by
  sorry

end TruthCore.Results.Causality.BearerRegress
