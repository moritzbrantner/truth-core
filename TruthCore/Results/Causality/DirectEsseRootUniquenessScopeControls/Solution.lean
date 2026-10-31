import TruthCore.Causality.DirectEsseRootUniquenessAtBeing
import TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.Solution
namespace TruthCore.Results.Causality.DirectEsseRootUniquenessScopeControls
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing.Controls
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)

private theorem causalAtBeing (loops : Bool) :
    MaximumInBeingCausesAllBeingsReading act (more loops) causes esse := by
  intro n hn x hx ha
  exact ⟨rfl, TruthCore.Models.QuartaViaMaximumControls.CrossedTops.genus esse n hn x hx ha⟩
private theorem gradesAtBeing (loops : Bool) : GradesToMaximumAtBeing act (more loops) esse :=
  TruthCore.Models.QuartaViaMaximumControls.CrossedTops.approach esse

private theorem population :
    TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt model.ontic model.concrete false :=
  ⟨false, trivial, trivial⟩
private theorem wholeRoster :
    TruthCore.Causality.WholeRosterFoundation.WholeRosterNotTrapped model false := by
  intro _ hTrap
  have hSource : (TruthCore.Causality.ConcreteExistentialSupply.graph model false).Source
      ⟨false, trivial, trivial⟩ := by
    rintro ⟨y, hy⟩
    exact Bool.noConfusion hy.2
  exact hTrap.1 ⟨false, trivial, trivial⟩ trivial hSource
private theorem dependence :
    TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt model false := by
  intro x _ _ hCont
  obtain ⟨_, v, _, hAbsent⟩ := hCont
  exact (hAbsent trivial).elim
private theorem existing :
    TruthCore.Causality.ExistenceActuality.ExistingInActAt model.ontic act esse false :=
  fun _ _ => trivial
private theorem esseGround :
    TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
      model false causes esse := by
  intro c x _ _ hCause
  exact ⟨trivial, trivial, hCause.2⟩
private theorem retained (loops : Bool) : Retained loops :=
  ⟨population, wholeRoster, dependence, causalAtBeing loops, existing, esseGround, gradesAtBeing loops⟩

private theorem globalGradesFlatOther : GradesByApproachToAMaximumReading act (more false) := by
  intro r
  cases r with
  | false =>
    rintro ⟨x, y, h⟩
    exact Bool.noConfusion h
  | true => exact gradesAtBeing false

private theorem notGlobalGenus : ¬ MaximumInGenusCausesAllInGenusReading act (more false) causes := by
  intro h
  have hm : IsMaximumIn act (more false) false false :=
    ⟨trivial, fun _ hy => Bool.noConfusion hy⟩
  have bad := h false false hm true (by decide) trivial
  exact Bool.noConfusion bad.1

private theorem globalGenusLoopOther : MaximumInGenusCausesAllInGenusReading act (more true) causes := by
  intro r n hn
  cases r with
  | false => exact (hn.2 n rfl).elim
  | true => exact causalAtBeing true n hn

private theorem notGlobalGrades : ¬ GradesByApproachToAMaximumReading act (more true) := by
  intro h
  obtain ⟨n, hn⟩ := h false ⟨false, false, rfl⟩
  exact hn.2 n rfl

theorem checks (hEM : ExcludedMiddle) : ScopeControls := by
  refine ⟨retained false, ⟨rfl, rfl⟩, globalGradesFlatOther, notGlobalGenus,
    retained true, ⟨rfl, rfl⟩, globalGenusLoopOther, notGlobalGrades, ?_⟩
  exact TruthCore.Results.Causality.DirectEsseRootUniquenessAtBeing.uniqueRoot
    model false act (more false) causes esse population wholeRoster dependence hEM
    (causalAtBeing false) existing esseGround (gradesAtBeing false)
end TruthCore.Results.Causality.DirectEsseRootUniquenessScopeControls
