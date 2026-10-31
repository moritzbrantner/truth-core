import TruthCore.Causality.RootIntellectWillOmission
import TruthCore.Results.Causality.NecessarySimplePlurality.Solution
import TruthCore.Results.Causality.DirectEsseGenusOmissionControl.Solution

namespace TruthCore.Results.Causality.RootIntellectWillOmission
open TruthCore.Causality.RootIntellectWillOmission
open TruthCore.Causality.NecessarySimplePlurality
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

private theorem firstLeft : IsFirstBeing component Being.left := by
  intro y hy
  exact (Nat.not_lt_zero (rank y) hy).elim
private theorem firstRight : IsFirstBeing component Being.right := by
  intro y hy
  exact (Nat.not_lt_zero (rank y) hy).elim

private theorem retained : RetainedInputs := by
  have hJoint := TruthCore.Results.Causality.NecessarySimplePlurality.jointControl
  rcases hJoint.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hDichotomy, hNoSelf⟩
  rcases hJoint.2.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hKinds, _⟩
  refine ⟨TruthCore.Results.Causality.DirectEsseGenusOmissionControl.population,
    TruthCore.Results.Causality.DirectEsseGenusOmissionControl.wholeRoster,
    TruthCore.Results.Causality.DirectEsseGenusOmissionControl.contingentDependence,
    TruthCore.Results.Causality.DirectEsseGenusOmissionControl.existingInAct,
    TruthCore.Results.Causality.DirectEsseGenusOmissionControl.esseGround,
    hDichotomy, hNoSelf, ?_, ?_, ?_, hKinds, ?_, ?_⟩
  · intro y x _ hy
    exact ⟨trivial, trivial, hy⟩
  · exact fun _ _ h => h
  · exact fun _ h => h
  · intro x hNotMatter hRemote
    cases x with
    | left => exact hRemote .instrument (by change 0 < 1; decide)
    | right => exact hRemote .instrument (by change 0 < 1; decide)
    | instrument => exact hNotMatter (by change 0 < 1; decide)
    | effect => exact hNotMatter (by change 0 < 2; decide)
  · exact fun _ h => h.elim

private theorem structureLeft : RootStructure Being.left := by
  refine ⟨TruthCore.Results.Causality.DirectEsseGenusOmissionControl.leftRoot,
    fun _ _ => trivial, firstLeft, ?_, rfl, ?_⟩
  · rintro ⟨y, hy, _⟩
    exact Nat.not_lt_zero (rank y) hy
  · change 0 < 1
    decide

private theorem structureRight : RootStructure Being.right := by
  refine ⟨TruthCore.Results.Causality.DirectEsseGenusOmissionControl.rightRoot,
    fun _ _ => trivial, firstRight, ?_, rfl, ?_⟩
  · rintro ⟨y, hy, _⟩
    exact Nat.not_lt_zero (rank y) hy
  · change 0 < 1
    decide

theorem checks (_hEM : ExcludedMiddle) : Control := by
  refine ⟨TruthCore.Results.Causality.NecessarySimplePlurality.jointControl,
    retained, structureLeft, structureRight, Being.noConfusion, ?_, ?_, ?_⟩
  · intro hL
    exact hL .left .instrument (by change 0 < 1; decide) firstLeft
  · rintro ⟨_, _, hIntellect⟩
    exact hIntellect
  · rintro ⟨_, _, _, _, _, _, _, _, hIntellect, _⟩
    exact hIntellect

end TruthCore.Results.Causality.RootIntellectWillOmission
