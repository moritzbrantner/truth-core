import TruthCore.Causality.GradedSupportFoundation
import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution
import TruthCore.Results.Causality.SpineRivalsRootEsse.Solution

namespace TruthCore.Results.Causality.GradedSupportFoundation

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.GradedSupportFoundation
open TruthCore.Causality.GradedSupportFoundation.Control
open TruthCore.Causality.Round2Grounding (ActualGroundIsMoreInEsse)
open TruthCore.Causality.Round3FourthWay (NoInfiniteAscentInBeing)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- The global no-infinite-ascent premise implies its restriction to actual
concreta at `w`. -/
theorem actualAscentWFOfGlobal {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hNIA : NoInfiniteAscentInBeing MoreIn esse) :
    NoInfiniteAscentAmongActualConcreta m w MoreIn esse := by
  sorry

/-- The global no-infinite-ascent premise implies its restriction to concreta
necessary from `w`. -/
theorem necessaryAscentWFOfGlobal {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hNIA : NoInfiniteAscentInBeing MoreIn esse) :
    NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse := by
  sorry

/-- Well-founded actual grounding, without a numeric rank: actual concrete
grounding at `w` ascends the rigid comparison `MoreIn esse`, which has no
infinite ascent among actual concreta at `w`. A descending grounding chain among
actual concreta would be an infinite ascent in esse among them. -/
theorem actualGroundingWFOfAscent {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : ActualGroundIsMoreInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongActualConcreta m w MoreIn esse) :
    ActualGroundingWF m w := by
  sorry

/-- J2 without the no-novel-edge condition: support between concreta necessary
from `w`, at every admitted world, ascends the same rigid comparison, which has no
infinite ascent among concreta necessary from `w`. Every edge of the cross-world
union is one ascent step. -/
theorem unionWFOfAscent {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    ConcreteNecessaryUnionWF m w := by
  sorry

/-- The mutual-support rival of J2 is excluded by a rigid well-founded grade
that support between necessary concreta ascends, with no reflexivity, actual
well-foundedness or no-novel-edge premise: two necessary concreta supporting
each other at two worlds would each be more in esse than the other. -/
theorem mutualSupportExcludedByGrade {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    NoNecessaryConcretaMutualSupport m w := by
  sorry

/-- The ascent premise from the Aristotelian cause principle: a distinct cause
of a quality in another is more such than it; an actual concrete ground of an
actual concretum is a distinct cause of its being. -/
theorem groundMoreInEsseOfCause {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hBridge : ActualGroundIsDistinctEsseCause m w CausesIn esse) :
    ActualGroundIsMoreInEsse m w MoreIn esse := by
  sorry

/-- Ascent of support at every world from the Aristotelian cause principle and
the every-world ground-cause bridge. -/
theorem everywhereAscentOfCause {W B R : Type} (m : Profile W B)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hBridge : SupportIsDistinctEsseCauseEverywhere m CausesIn esse) :
    SupportAscendsInEsseEverywhere m MoreIn esse := by
  sorry

/-- Ascent of support at every world implies ascent of support between
necessary concreta. -/
theorem necessaryAscentOfEverywhere {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hU : SupportAscendsInEsseEverywhere m MoreIn esse) :
    NecessarySupportAscendsInEsse m w MoreIn esse := by
  sorry

/-- Ascent of support at every world implies ascent of actual grounding at `w`. -/
theorem actualAscentOfEverywhere {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hU : SupportAscendsInEsseEverywhere m MoreIn esse) :
    ActualGroundIsMoreInEsse m w MoreIn esse := by
  sorry

/-- Converse characterization: well-founded actual grounding yields a rigid
grade with no infinite ascent that actual grounding ascends (actual grounding
itself, extended by nothing). -/
theorem gradedOfActualGroundingWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : GradedActualGrounding m w := by
  sorry

/-- Converse characterization: J2 yields a rigid grade with no infinite ascent
that support between necessary concreta ascends (the union itself). -/
theorem gradedOfUnionWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ConcreteNecessaryUnionWF m w) : GradedNecessarySupport m w := by
  sorry

/-! ## Controls -/

/-- All graded-foundation controls hold. -/
theorem controls : Controls := by
  sorry

end TruthCore.Results.Causality.GradedSupportFoundation
