module

public import TruthCore.Teleonomy.DirectorRivalBoundary
public import TruthCore.Results.Comparison.Teleonomy.DirectorRivalBoundary.ExactRival.Solution
public import TruthCore.Results.Comparison.Teleonomy.UnguidedFinality.Solution
public import TruthCore.Results.Comparison.Teleonomy.GovernedMechanisms.Solution

@[expose] public section
namespace TruthCore.Results.Comparison.Teleonomy.DirectorRivalBoundary.Controls
open TruthCore.Teleonomy
open TruthCore.Teleonomy.DirectorRivalBoundary
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
theorem controls : Controls := by
  have witness : UndirectedTendingWitness noneP noneP bodyEnd noDirects := by
    refine ⟨.b0, (), ?_, True.intro, ?_⟩
    · intro h
      exact h
    · intro ⟨d, hCognition, _, _⟩
      exact hCognition
  refine ⟨?_, witness, ExactRival.exactRival noneP noneP bodyEnd noDirects witness,
    TruthCore.Results.Comparison.Teleonomy.UnguidedFinality.unguidedFinality,
    TruthCore.Results.Comparison.Teleonomy.GovernedMechanisms.governedMechanisms⟩
  refine ⟨(fun _ => False), (fun _ => False), (fun _ _ => False),
    (fun _ _ _ => False), ?_, ?_, ?_⟩
  · intro x h
    exact h
  · intro x e h
    exact h
  · intro x e hNo hTends
    exact False.elim hTends
end TruthCore.Results.Comparison.Teleonomy.DirectorRivalBoundary.Controls
