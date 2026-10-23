import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Interpretive argument: given the textual premises and the charity principle,
the formal facts about the two readings make the strong reading the intended one.
Lean checks only this consequence; the textual premises are source-fidelity claims. -/
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
/-- Discharges the formal premise `hStrong`. -/
theorem strongReadingYieldsUnmovedMover : StrongReadingYieldsUnmovedMover :=
  PrimaViaModels.strongReadingYields
/-- Discharges the formal premise `hWeak` by the finite `weakModel`. -/
theorem weakReadingDoesNotYieldUnmovedMover : WeakReadingDoesNotYieldUnmovedMover :=
  PrimaViaModels.weakReadingDoesNotYield
end TruthCore.Results.Aquinas.SummaTheologiae.StrongReadingIntended
