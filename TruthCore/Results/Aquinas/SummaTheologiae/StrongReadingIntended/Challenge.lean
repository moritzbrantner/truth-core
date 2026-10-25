import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
namespace TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
open TruthCore.Latin.Aquinas.SummaTheologiae
theorem strongReadingIntended
    (StatesUnrestricted PresentsAsNecessary WordingAdmitsStrong NoTextForcesWeak
      StrongIntended : Prop)
    (hWording : PrimaViaStatesUnrestrictedUnmovedMoverReading StatesUnrestricted)
    (hNecessary : PrimaViaPresentsConclusionAsNecessaryReading PresentsAsNecessary)
    (hAdmits : PrimaViaDependenceWordingAdmitsStrongReading WordingAdmitsStrong)
    (hQ46 : Q46DoesNotForceWeakReadingReading NoTextForcesWeak)
    (hStrong : StrongReadingYieldsUnmovedMover)
    (hWeak : WeakReadingDoesNotYieldUnmovedMover)
    (hCharity : ValidityCharityPrinciple StatesUnrestricted PresentsAsNecessary
      WordingAdmitsStrong NoTextForcesWeak StrongIntended) :
    StrongPerSeReadingIntendedReading StrongIntended := by
  sorry
end TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
