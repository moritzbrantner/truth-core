module

public import TruthCore.Logic.MeaningDefinitionFork

@[expose] public section
namespace TruthCore.Results.Logic.MeaningDefinitionFork.Controls
open TruthCore.Logic.Verificationism
open TruthCore.Logic.MeaningDefinitionFork
open TruthCore.Logic.MeaningDefinitionFork.Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent

theorem observedNotAnalytic : ¬ analyticOnly observed := by
  intro h
  exact Bool.noConfusion (h (false, false))

theorem observedObservation : observableFrame.observation observed := by
  intro a b c
  rfl

theorem observedConclusive : ConclusivelyVerifiable observableFrame observed := by
  refine ⟨[observed], ?_, ⟨(true, false), ?_⟩, ?_⟩
  · intro o ho
    cases ho with
    | head => exact observedObservation
    | tail _ h => cases h
  · intro o ho
    cases ho with
    | head => rfl
    | tail _ h => cases h
  · intro w hw
    exact hw observed (List.Mem.head [])

theorem observedWeak : WeaklyVerifiable1936 observableFrame observed := by
  refine ⟨[], observed, observedObservation, ?_, ?_⟩
  · intro w hw
    exact hw observed (List.Mem.head [])
  · intro h
    exact Bool.noConfusion (h (false, false) (fun _ hg => by cases hg))

theorem observedLiteral : LiterallyMeaningful1946 observableFrame observed :=
  Or.inr (Or.inl (Or.inl observedObservation))

theorem controls : Properties := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, observedNotAnalytic,
    observedConclusive, observedWeak, observedLiteral⟩
  · intro s hs hm
    exact Or.inl hm
  · intro h
    exact observedNotAnalytic ((h observed True.intro).mpr (Or.inr observedConclusive))
  · intro h
    exact observedNotAnalytic ((h observed True.intro).mpr (Or.inr observedWeak))
  · intro h
    exact observedNotAnalytic ((h observed True.intro).mpr observedLiteral)
  · intro h
    exact observedNotAnalytic (h observed True.intro)
  · intro w
    rfl

end TruthCore.Results.Logic.MeaningDefinitionFork.Controls
