module

public import TruthCore.Logic.ScopedEmpiricalProofBarrier

@[expose] public section
namespace TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Coverage
open TruthCore.Logic.Verificationism
open TruthCore.Logic.ScopedEmpiricalProofBarrier
theorem domainFork (hEM : TruthCore.Logic.ExcludedMiddle) : DomainFork := by
  intro L q T
  rcases hEM (SubjectDefinition q T) with hs | hs
  · exact Or.inl (Or.inl hs)
  rcases hEM (PremiseDefinition q T) with hp | hp
  · exact Or.inl (Or.inr (Or.inl hp))
  rcases hEM (MethodDefinition q T) with hm | hm
  · exact Or.inl (Or.inr (Or.inr hm))
  · exact Or.inr ⟨hs, hp, hm⟩
end TruthCore.Results.Logic.ScopedEmpiricalProofBarrier.Coverage
