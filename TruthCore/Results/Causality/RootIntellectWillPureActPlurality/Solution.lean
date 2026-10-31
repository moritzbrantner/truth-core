import TruthCore.Causality.RootIntellectWillPureActPlurality
import TruthCore.Results.Causality.PartFreePlurality.Solution
namespace TruthCore.Results.Causality.RootIntellectWillPureActPlurality
open TruthCore.Causality.RootIntellectWillPureActPlurality
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Latin.Aquinas.SummaTheologiae

private theorem retained : RetainedInputs := by
  have hPop : TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt
      model.ontic model.concrete false := ⟨Being.left, trivial, trivial⟩
  have hWhole : TruthCore.Causality.WholeRosterFoundation.WholeRosterNotTrapped model false := by
    intro _ hTrap
    have hSource : (graph model false).Source ⟨Being.left, trivial, trivial⟩ := by
      rintro ⟨y, hy⟩
      exact Nat.not_lt_zero (rank y.val) hy
    exact hTrap.1 ⟨Being.left, trivial, trivial⟩ trivial hSource
  have hDep : TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt model false := by
    intro x _ _ hCont
    obtain ⟨_, v, _, hAbsent⟩ := hCont
    exact (hAbsent trivial).elim
  refine ⟨hPop, hWhole, hDep, ?_, ?_, ?_,
    TruthCore.Results.Causality.PartFreePlurality.kinds,
    TruthCore.Results.Causality.PartFreePlurality.noComponentFirst, ?_, ?_,
    TruthCore.Results.Causality.PartFreePlurality.actPrior, ?_,
    TruthCore.Results.Causality.PartFreePlurality.notBoth⟩
  · intro y x _ hy
    exact ⟨trivial, trivial, hy⟩
  · exact fun _ _ h => h.2
  · exact fun _ h => h
  · intro x hNotMatter hRemote
    cases x with
    | left => trivial
    | right => trivial
    | constituent =>
      exact (hRemote .instrument ⟨by change 0 < 1; decide, by change 1 < 2; decide⟩).elim
    | instrument => exact (hNotMatter (by change 1 < 2; decide)).elim
    | effect => exact (hNotMatter (by change 1 < 3; decide)).elim
  · exact fun _ h => h
  · refine ⟨?_⟩
    intro x hx
    exact Nat.lt_irrefl (rank x) hx

private theorem leftWitness : Witness Being.left := by
  refine ⟨⟨⟨trivial, trivial⟩, ?_⟩, (fun _ _ => trivial), rfl, ?_, ?_, ?_,
    ?_, trivial, trivial, ?_⟩
  · intro y hy
    exact Nat.not_lt_zero (rank y) hy.2.2
  · rintro ⟨p, hp, _⟩
    exact Nat.not_lt_zero (rank p) hp.2
  · intro y hy
    exact (Nat.not_lt_zero (rank y) hy).elim
  · intro h
    exact Nat.not_lt_zero 1 h
  · intro y h
    exact Nat.lt_irrefl 0 h.1
  · intro r h
    cases r <;> exact h

private theorem rightWitness : Witness Being.right := by
  refine ⟨⟨⟨trivial, trivial⟩, ?_⟩, (fun _ _ => trivial), rfl, ?_, ?_, ?_,
    ?_, trivial, trivial, ?_⟩
  · intro y hy
    exact Nat.not_lt_zero (rank y) hy.2.2
  · rintro ⟨p, hp, _⟩
    exact Nat.not_lt_zero (rank p) hp.2
  · intro y hy
    exact (Nat.not_lt_zero (rank y) hy).elim
  · intro h
    exact Nat.not_lt_zero 1 h
  · intro y h
    exact Nat.lt_irrefl 0 h.1
  · intro r h
    cases r <;> exact h

theorem checks (_hEM : ExcludedMiddle) : Control := by
  refine ⟨TruthCore.Results.Causality.PartFreePlurality.jointControl, retained,
    leftWitness, rightWitness, Being.noConfusion, ?_, trivial, trivial, ?_, trivial, ?_⟩
  · exact ⟨Being.left, leftWitness⟩
  · change 0 < 2
    decide
  · exact ⟨by change 0 < 1; decide, by change 1 < 2; decide⟩
end TruthCore.Results.Causality.RootIntellectWillPureActPlurality
