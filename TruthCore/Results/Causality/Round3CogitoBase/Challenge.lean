import TruthCore.Causality.Round3CogitoBase
import TruthCore.Results.Causality.ConcreteExistentialSupply.Solution
import TruthCore.Results.Causality.SelectedAncestry.Solution

namespace TruthCore.Results.Causality.Round3CogitoBase
open TruthCore.Causality.Round3CogitoBase
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete ActualGroundingWF)
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.SelectedAncestry (ConeWellFounded ConeContingentGrounded)
open TruthCore.Causality.ConcreteExistentialSupply (ActualConcreteBorrowingEscape)
open TruthCore.Results.Causality.ConcreteExistentialSupply (borrowingEscapeWFEquivalence)
open TruthCore.Results.Causality.SelectedAncestry (scopeComparison)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs)
open TruthCore.Logic.CogitoConcrete (EveryBearerIsConcrete EveryBearerExistsAt BorneThoughtIsOpining)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

/-- Cogito by retorsion. A doubt whether any thought occurs is performed; a
performed doubt of that kind is realized by an occurring thought episode;
hence some thought episode occurs. Two OPEN premises; the middle term is the
performed doubting act. -/
theorem thoughtOccursFromPerformedDoubt {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop)
    (Realizes : Act → Episode → Prop)
    (hDoubt : DoubtIsPerformed Performed DoubtsThought)
    (hThought : PerformedDoubtIsThought Performed DoubtsThought Occurs Realizes) :
    ThoughtOccurs Occurs := by
  sorry

/-- The retorsion itself: if a performed doubt whether thought occurs is
realized by an occurring thought, then performing that doubt falsifies its
content "no thought episode occurs". Whether any doubt is performed is not
assumed. -/
theorem performedDoubtSelfRefuting {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop)
    (Realizes : Act → Episode → Prop)
    (hThought : PerformedDoubtIsThought Performed DoubtsThought Occurs Realizes) :
    PerformedDoubtOfThoughtSelfRefuting Performed DoubtsThought Occurs := by
  sorry

/-- Every occurring thought is an assenting episode; the bearer of an
assenting episode opines its content; hence whoever bears an occurring thought
opines its content. A chain through the distinct middle term `Assenting`. -/
theorem borneThoughtIsOpiningFromAssent {E Episode : Type}
    (Occurs Assenting : Episode → Prop) (Bears : E → Episode → Prop)
    (Opines : E → Prop → Prop) (content : Episode → Prop)
    (hAssent : OccurringThoughtIsAssenting Occurs Assenting)
    (hOpines : AssentingBearerOpinesContent Bears Assenting Opines content) :
    BorneThoughtIsOpining Occurs Bears Opines content := by
  sorry

/-- The selected being bears an occurring thought; every bearer of an
occurring thought is concrete and exists at `w`; hence the selected being is an
actual concretum at `w`. -/
theorem selectedActualConcreteFromBorneThought {W B Episode : Type}
    (m : Profile W B) (w : W) (selected : B)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (hSel : SelectedBearsOccurringThought Occurs Bears selected)
    (hConc : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hEx : EveryBearerExistsAt m.ontic Occurs Bears w) :
    ActualConcrete m w selected := by
  sorry

/-- A natural-number rank strictly decreasing along actual concrete grounding
makes actual grounding well-founded (inverse image of `<` on `Nat`). No
excluded middle. -/
theorem actualGroundingWFFromFiniteRank {W B : Type} (m : Profile W B) (w : W)
    (hRank : ActualGroundingFiniteRank m w) : ActualGroundingWF m w := by
  sorry

/-- The finite rank and excluded middle give the no-self-contained-borrowing
cut: the rank gives well-founded actual grounding, and the existing
equivalence (`borrowingEscapeWFEquivalence`, which needs excluded middle)
turns it into the cut. -/
theorem borrowingEscapeFromFiniteRank {W B : Type} (m : Profile W B) (w : W)
    (hRank : ActualGroundingFiniteRank m w) (hEM : ExcludedMiddle) :
    ActualConcreteBorrowingEscape m w := by
  sorry

/-- Global well-founded actual grounding restricts to the selected cone
(the cone is a subset of the actual concreta; `scopeComparison`). The strong
version is the only premise. -/
theorem selectedConeWFFromGlobalWF {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hWF : ActualGroundingWF m w) : ConeWellFounded m w selected := by
  sorry

/-- If the selected cone has no contingent root ancestor, then (with excluded
middle) every contingent cone member has an actual concrete ground: an
ungrounded one would be a contingent root ancestor. -/
theorem coneContingentGroundedFromNoContingentRoot {W B : Type} (m : Profile W B) (w : W)
    (selected : B) (hNo : NoContingentRootAncestor m w selected) (hEM : ExcludedMiddle) :
    ConeContingentGrounded m w selected := by
  sorry

/-- Potency is capacity under privation, and privation in a capable subject
is lack of the act; hence potency is unactualized capacity. A chain through
the distinct middle term `Deprived`. -/
theorem potencyIsUnactualizedCapacityFromPrivation {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hPriv : PotencyIsCapacityUnderPrivation InPotency CanBe Deprived)
    (hLack : PrivationIsLackOfActInCapable InAct CanBe Deprived) :
    PotencyIsUnactualizedCapacityReading InAct InPotency CanBe := by
  sorry

/-- Being moved is the actualization of an unactualized capacity, and potency
is unactualized capacity; hence being moved is the actualization of a potency
(*Physics* III.1 reading). A chain through the middle term "unactualized
capacity". -/
theorem beingMovedFromUnactualizedCapacity {Being Respect : Type}
    (MovedIn InAct InPotency CanBe ActualizedQuaPotential : Being → Respect → Prop)
    (hMoved : BeingMovedIsActualizationOfUnactualizedCapacity MovedIn InAct CanBe
      ActualizedQuaPotential)
    (hPot : PotencyIsUnactualizedCapacityReading InAct InPotency CanBe) :
    BeingMovedIsActualizationOfPotencyReading MovedIn InPotency ActualizedQuaPotential := by
  sorry

/-! ## Controls -/

namespace Control
open TruthCore.Causality.Round3CogitoBase.Control

end Control

/-- Omission models for every load-bearing premise other than excluded middle,
and joint nonvacuity witnesses for the three vocabularies. -/
theorem controls : TruthCore.Causality.Round3CogitoBase.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.Round3CogitoBase
