import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Causality.NecessaryConcreteRouteBridge

namespace TruthCore.Results.Causality.WholeRosterFoundation
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ConcreteExistentialSupply
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae (MaximumInGenusCausesAllInGenusReading)
open TruthCore.Case.Catholicism (MaximumInBeingIsFirstBeing NecessaryBeingHasBeing
  CauseOfNecessaryBeingCausesItsNecessity)

/-- The existing all-subsets cut implies its whole-roster restriction. -/
theorem wholeRosterOfBorrowingEscape {W B : Type} (m : Profile W B) (w : W)
    (hEscape : ActualConcreteBorrowingEscape m w) : WholeRosterNotTrapped m w := by
  intro hNonempty hTrap
  rcases hEscape Set.univ (fun _ _ => trivial) hNonempty with
      ⟨source, hMem, hSource⟩ | ⟨g, hAdmitted, hEffect, hOutside⟩
  · exact hTrap.1 source hMem hSource
  · obtain ⟨contributor, hMember, hInside⟩ := hTrap.2 g hAdmitted hEffect
    exact hOutside contributor hMember hInside

/-- Whole-roster nontrapping and actual concrete population supply a selected
actual root. No contingent-dependence or modal-necessity premise is used. -/
theorem actualRootExists {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w) (hEM : ExcludedMiddle) :
    ∃ n, ActualRoot m w n := by
  obtain ⟨initial, hc, he⟩ := hPop
  have hNonempty : (Set.univ : Set {b // ActualConcrete m w b}).Nonempty :=
    ⟨⟨initial, hc, he⟩, trivial⟩
  have hSource : ∃ source, (graph m w).Source source := by
    rcases hEM (∃ source, (graph m w).Source source) with h | h
    · exact h
    · apply False.elim
      apply hWhole hNonempty
      refine ⟨fun source _ hs => h ⟨source, hs⟩, ?_⟩
      intro g _ _
      obtain ⟨contributor, hMember⟩ := g.property
      exact ⟨contributor, hMember, trivial⟩
  obtain ⟨source, hs⟩ := hSource
  have hr : ActualRoot m w source.val := by
    refine ⟨source.property, ?_⟩
    intro candidate hGround
    exact hs ⟨⟨candidate, hGround.1, hGround.2.1⟩, hGround.2.2⟩
  exact ⟨source.val, hr⟩

/-- Non-corpus helper preserving the very same actual necessary root for
convergence. The only roster test is at Set.univ; no inductive Supply is used. -/
theorem necessaryActualRoot {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryActualRootAt m w := by
  obtain ⟨source, hr⟩ := actualRootExists m w hPop hWhole hEM
  rcases hEM (TruthCore.German.Kant.CosmologicalInference.NecessaryAt m.ontic w source)
      with hn | hn
  · exact ⟨source, hr, hn⟩
  · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
      (contingentRootOfNonnecessary m w hEM ⟨source, hr, hn⟩)).elim

/-- Whole-roster nontrapping, actual population and contingent dependence give
an actual necessary concretum. No all-subsets cut or WF premise is used. -/
theorem necessaryConcrete {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  obtain ⟨n, hr, hn⟩ := necessaryActualRoot m w hPop hWhole hDep hEM
  exact ⟨n, hr.1.1, hr.1.2, hn⟩

/-- The same necessary root feeds the existing per-se/convergence proof and
simply-prior bridge. No maximum existence or full explanatory completion follows. -/
theorem maximumFirst {W B Respect : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → Respect → Prop)
    (MoreIn : Respect → B → B → Prop) (CausesIn : B → B → Respect → Prop)
    (PriorSimply : B → B → Prop) (esse : Respect)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hBridge : NecessityCausesAreActualConcreteGrounds m w CausesNecessityOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hHasBeing : NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse)
    (hCause : CauseOfNecessaryBeingCausesItsNecessity (modalPossible m w) (modalIsAt m)
      CausesIn esse CausesNecessityOf) :
    MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply := by
  obtain ⟨n, hr, hn⟩ := necessaryActualRoot m w hPop hWhole hDep hEM
  obtain ⟨_, hIdent⟩ := necessaryRootIsMaximumOfRoot m w CausesNecessityOf
    InAct MoreIn CausesIn esse n hr hn hEM hBridge hGenus hHasBeing hCause
  intro x hMax y hy
  rcases hEM (y = x) with h | hne
  · exact h
  · have g := hPrior y x hne hy
    have hxr : x = n := hIdent x hMax
    subst hxr
    exact (hr.2 y g).elim

end TruthCore.Results.Causality.WholeRosterFoundation
