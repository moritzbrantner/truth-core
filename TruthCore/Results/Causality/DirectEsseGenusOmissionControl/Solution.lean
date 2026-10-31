import TruthCore.Causality.DirectEsseGenusOmissionControl
import TruthCore.Results.Causality.NecessarySimplePlurality.Solution
import TruthCore.Results.Causality.DirectEsseRootUniqueness.Solution

namespace TruthCore.Results.Causality.DirectEsseGenusOmissionControl
open TruthCore.Causality.DirectEsseGenusOmissionControl
open TruthCore.Logic (ExcludedMiddle)

open TruthCore.Causality.NecessarySimplePlurality
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.NecessaryRootUniqueness (UniqueNecessaryActualRootAt)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem leftRoot : ActualRoot profile false Being.left := by
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  intro y hy
  exact Nat.not_lt_zero (rank y) hy.2.2

theorem rightRoot : ActualRoot profile false Being.right := by
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  intro y hy
  exact Nat.not_lt_zero (rank y) hy.2.2

theorem population : InhabitedConcreteAt profile.ontic profile.concrete false :=
  ⟨Being.left, trivial, trivial⟩

theorem wholeRoster : WholeRosterNotTrapped profile false := by
  intro _ hTrap
  have hSource : (graph profile false).Source ⟨Being.left, trivial, trivial⟩ := by
    rintro ⟨y, hy⟩
    exact Nat.not_lt_zero (rank y.val) hy
  exact hTrap.1 ⟨Being.left, trivial, trivial⟩ trivial hSource

/-- Vacuous because the original interpretation has EVERY candidate at EVERY
world, not because any absent/abstract cause is admitted. -/
theorem contingentDependence : EveryContingentGroundedAt profile false := by
  intro x _ _ hCont
  obtain ⟨_, v, _, hAbsent⟩ := hCont
  exact (hAbsent trivial).elim

theorem existingInAct : ExistingInActAt profile.ontic inAct Respect.esse false := by
  intro x _
  cases x <;> trivial

/-- Direct esse cause and old esse support have the SAME old assignment.
This proves this instance, not the metaphysical identification in general. -/
theorem esseGround : EsseCauseIsActualConcreteGround profile false
    esseProfile.CausesIn Respect.esse := by
  intro c x _ _ hCause
  exact ⟨trivial, trivial, hCause⟩

theorem leftMaximum (r : Respect) : IsMaximumIn inAct moreIn r Being.left := by
  refine ⟨trivial, ?_⟩
  intro y hy
  exact Nat.not_lt_zero (rank y) hy.2.2

theorem rightMaximum (r : Respect) : IsMaximumIn inAct moreIn r Being.right := by
  refine ⟨trivial, ?_⟩
  intro y hy
  exact Nat.not_lt_zero (rank y) hy.2.2

theorem gradesMaximum : GradesByApproachToAMaximumReading inAct moreIn := by
  intro r _
  exact ⟨Being.left, leftMaximum r⟩

theorem notUniqueRoot : ¬ UniqueNecessaryActualRootAt profile false := by
  rintro ⟨n, _, _, hUnique⟩
  exact Being.noConfusion ((hUnique Being.left leftRoot).trans
    (hUnique Being.right rightRoot).symm)

/-- Consume the EXACT imported eight-input theorem with all seven remaining
inputs in this SAME interpretation. Genus causality would force the excluded
unique actual-root conclusion, so I fails here. -/
theorem notGenus (hEM : ExcludedMiddle) :
    ¬ MaximumInGenusCausesAllInGenusReading inAct moreIn esseProfile.CausesIn := by
  intro hGenus
  exact notUniqueRoot
    (TruthCore.Results.Causality.DirectEsseRootUniqueness.uniqueRoot
      profile false inAct moreIn esseProfile.CausesIn Respect.esse
      population wholeRoster contingentDependence hEM hGenus existingInAct esseGround gradesMaximum)

theorem checks (hEM : ExcludedMiddle) : Control := by
  exact ⟨TruthCore.Results.Causality.NecessarySimplePlurality.jointControl,
    ⟨population, wholeRoster, contingentDependence, existingInAct, esseGround, gradesMaximum⟩,
    ⟨trivial, trivial, by change 0 < 1; decide⟩,
    leftMaximum Respect.esse, rightMaximum Respect.esse,
    leftRoot, rightRoot, Being.noConfusion, notUniqueRoot, notGenus hEM⟩

end TruthCore.Results.Causality.DirectEsseGenusOmissionControl
