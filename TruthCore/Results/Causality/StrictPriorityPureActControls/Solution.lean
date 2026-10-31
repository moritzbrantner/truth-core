import TruthCore.Causality.StrictPriorityPureAct
import TruthCore.Results.Causality.DirectEsseGenusOmissionControl.Solution
import TruthCore.Results.Causality.NecessarySimplePlurality.Solution
namespace TruthCore.Results.Causality.StrictPriorityPureActControls
open TruthCore.Causality.StrictPriorityPureAct
open TruthCore.Causality.StrictPriorityPureAct.Controls
open TruthCore.Causality.NecessarySimplePlurality
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
private theorem loopBridge :
    TruthCore.Causality.NecessaryConcreteRouteBridge.SimplyPriorIsActualConcreteGround
      model false loopPriority := by
  intro y x hNe hPrior
  rcases hPrior with h | ⟨hEq, _⟩
  · exact ⟨trivial, trivial, h⟩
  · exact (hNe hEq).elim
private theorem strictBridge :
    TruthCore.Causality.NecessaryConcreteRouteBridge.SimplyPriorIsActualConcreteGround
      model false component := by
  intro y x _ h
  exact ⟨trivial, trivial, h⟩
private theorem loopActPrior : ActSimplyPriorToPotencyReading inAct moved loopPriority := by
  intro x r hp
  obtain ⟨y, ha, hy⟩ := TruthCore.Results.Causality.NecessarySimplePlurality.actPrior x r hp
  exact ⟨y, ha, Or.inl hy⟩
private theorem strictActPrior : ActSimplyPriorToPotencyReading allAct moved component := by
  intro x r hp
  obtain ⟨y, _, hy⟩ := TruthCore.Results.Causality.NecessarySimplePlurality.actPrior x r hp
  exact ⟨y, trivial, hy⟩
theorem checks (_hEM : ExcludedMiddle) : Separation := by
  have hPop := TruthCore.Results.Causality.DirectEsseGenusOmissionControl.population
  have hWhole := TruthCore.Results.Causality.DirectEsseGenusOmissionControl.wholeRoster
  have hDep := TruthCore.Results.Causality.DirectEsseGenusOmissionControl.contingentDependence
  refine ⟨⟨hPop, hWhole, hDep, loopBridge, loopActPrior⟩,
    TruthCore.Results.Causality.NecessarySimplePlurality.notBoth, ?_,
    ⟨hPop, hWhole, hDep, strictBridge, strictActPrior⟩, ?_, ?_⟩
  · intro h
    exact h.irrefl Being.instrument (Or.inr ⟨rfl, rfl⟩)
  · refine ⟨?_⟩
    intro x hx
    exact Nat.lt_irrefl (rank x) hx
  · intro h
    exact h Being.instrument Respect.drive ⟨trivial, trivial⟩
end TruthCore.Results.Causality.StrictPriorityPureActControls
