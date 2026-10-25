import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
namespace TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Interpretive argument: given the textual premises and the charity principle,
the formal facts about the two readings make the strong reading the intended one.
Lean checks only this consequence; the textual premises are source-fidelity claims.
The two formal premises `hStrong` and `hWeak` are premise-free results of their own
(`PrimaViaFacts.StrongReadingYields`, `PrimaViaFacts.WeakReadingDoesNotYield`). -/
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
    StrongPerSeReadingIntendedReading StrongIntended :=
  hCharity hWording hNecessary hAdmits hStrong hWeak hQ46
end TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
