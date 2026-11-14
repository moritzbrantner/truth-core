module

public import TruthCore.Logic.DarwinianEpistemicDebunking
public import TruthCore.Results.Logic.GlobalThesisBoundaries.Solution

/-!
Street's Darwinian dilemma extended to epistemic evaluative judgments (#1585).
The first horn yields a tracking failure from origin fixing and
within-history variation of correctness. Applied uniformly to the debunker's
own epistemic basis, the debunker's defeat policy composes with the existing
sole-basis warrant result. History-fixed correctness blocks the tracking
failure. Analyst formulations; attribution deferred.
-/

@[expose] public section

namespace TruthCore.Results.Logic.DarwinianEpistemicDebunking

open TruthCore.Logic.DarwinianEpistemicDebunking
open TruthCore.Logic.GlobalThesisBoundaries
open TruthCore.Logic.EpistemicReasons

theorem selectionWithVariationYieldsMismatch (P : DarwinianProfile) :
    SelectionFixesVerdict P →
    CorrectnessVariesWithinHistory P →
    HistoryMateMismatch P := by
  intro hFix ⟨s, hMate, hVary⟩
  by_cases hActual : P.verdict P.actual = P.correct P.actual
  · refine ⟨s, hMate, ?_⟩
    rw [hFix s hMate, hActual]
    exact fun h => hVary h.symm
  · exact ⟨P.actual, rfl, hActual⟩

theorem realistDebunkerLacksOwnWarrant (f : ReliabilityFrame) (a : f.Agent)
    (prof : f.Basis → DarwinianProfile) (conclusion : f.Content) (E : f.Basis) :
    UniformMismatchPolicy f a prof →
    SelectionFixesVerdict (prof E) →
    CorrectnessVariesWithinHistory (prof E) →
    SoleSupportingBasis f a conclusion E →
    WarrantNeedsUndefeatedSupport f a conclusion →
    LacksTargetWarrant f a conclusion := by
  intro hPolicy hFix hVary hSole hNeeds
  have hUndercut : BasisUndercut f a E :=
    hPolicy E (selectionWithVariationYieldsMismatch (prof E) hFix hVary)
  exact TruthCore.Results.Logic.GlobalThesisBoundaries.undercutSoleBasisPrecludesWarrant
    f a conclusion E hUndercut hSole hNeeds

theorem historyFixedCorrectnessKeepsHistoryMatesAccurate (P : DarwinianProfile) :
    SelectionFixesVerdict P →
    CorrectnessFixedByHistory P →
    ActuallyAccurate P →
    HistoryMatesAccurate P := by
  intro hFix hCorrect hActual s hMate
  rw [hFix s hMate, hCorrect s hMate]
  exact hActual

theorem darwinianDebunkingControls : DarwinianDebunkingControls := by
  have hSole (concern defeat : Bool) :
      SoleSupportingBasis (reliabilityControl concern defeat false) () true true := by
    intro b h
    rcases h with h | ⟨_, h | h⟩
    · exact h.1
    · cases h
    · cases h
  have hFixedAccurate : HistoryMatesAccurate fixedTrue := fun _ _ => rfl
  have hNoMismatch : ¬ HistoryMateMismatch fixedTrue := by
    rintro ⟨s, _, h⟩
    exact h rfl
  refine ⟨⟨fun _ _ => rfl, ⟨false, rfl, by decide⟩, rfl, ⟨false, rfl, by decide⟩⟩,
    ⟨?_, ⟨false, rfl, by decide⟩, fun _ _ => rfl⟩,
    ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, hNoMismatch⟩,
    ⟨?_, fun _ _ => rfl, ⟨false, rfl, by decide⟩, hSole true true, ?_, ?_, trivial, ?_⟩,
    ⟨fun _ h => absurd h hNoMismatch, fun _ _ => rfl, fun _ _ => rfl, hSole false false,
      fun _ => ⟨true, Or.inl ⟨rfl, rfl⟩, fun h => Bool.noConfusion h.2⟩,
      Or.inr (Or.inl rfl)⟩⟩
  · intro h
    exact Bool.noConfusion (h false rfl)
  · intro E hMismatch
    cases E
    · exact absurd hMismatch hNoMismatch
    · exact ⟨rfl, rfl⟩
  · intro h
    rcases h with h | h | h <;> cases h
  · intro h
    rcases h with h | h | h <;> cases h
  · exact ⟨(), false, false, Or.inr ⟨rfl, Or.inl rfl⟩, fun h => Bool.noConfusion h.1⟩

end TruthCore.Results.Logic.DarwinianEpistemicDebunking
