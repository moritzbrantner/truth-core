module

public import TruthCore.Causality.Round3CogitoBase
public import TruthCore.Results.Causality.ConcreteExistentialSupply.Solution
public import TruthCore.Results.Causality.SelectedAncestry.Solution

@[expose] public section

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
  obtain ⟨a, hp, hd⟩ := hDoubt
  obtain ⟨e, he, _⟩ := hThought a hp hd
  exact ⟨e, he⟩

/-- The retorsion itself: if a performed doubt whether thought occurs is
realized by an occurring thought, then performing that doubt falsifies its
content "no thought episode occurs". Whether any doubt is performed is not
assumed. -/
theorem performedDoubtSelfRefuting {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop)
    (Realizes : Act → Episode → Prop)
    (hThought : PerformedDoubtIsThought Performed DoubtsThought Occurs Realizes) :
    PerformedDoubtOfThoughtSelfRefuting Performed DoubtsThought Occurs := by
  intro a hp hd hNone
  obtain ⟨e, he, _⟩ := hThought a hp hd
  exact hNone ⟨e, he⟩

/-- Every occurring thought is an assenting episode; the bearer of an
assenting episode opines its content; hence whoever bears an occurring thought
opines its content. A chain through the distinct middle term `Assenting`. -/
theorem borneThoughtIsOpiningFromAssent {E Episode : Type}
    (Occurs Assenting : Episode → Prop) (Bears : E → Episode → Prop)
    (Opines : E → Prop → Prop) (content : Episode → Prop)
    (hAssent : OccurringThoughtIsAssenting Occurs Assenting)
    (hOpines : AssentingBearerOpinesContent Bears Assenting Opines content) :
    BorneThoughtIsOpining Occurs Bears Opines content := by
  intro b e he hb
  have hAssenting : Assenting e := hAssent e he
  exact hOpines b e hb hAssenting

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
  obtain ⟨e, he, hb⟩ := hSel
  exact ⟨hConc selected e he hb, hEx selected e he hb⟩

/-- A natural-number rank strictly decreasing along actual concrete grounding
makes actual grounding well-founded (inverse image of `<` on `Nat`). No
excluded middle. -/
theorem actualGroundingWFFromFiniteRank {W B : Type} (m : Profile W B) (w : W)
    (hRank : ActualGroundingFiniteRank m w) : ActualGroundingWF m w := by
  obtain ⟨rank, hDesc⟩ := hRank
  have hNat : WellFounded (InvImage (· < ·) fun a : {x // ActualConcrete m w x} => rank a.1) :=
    InvImage.wf _ Nat.lt_wfRel.wf
  exact Subrelation.wf (fun {a b} h => hDesc b.1 a.1 b.2 a.2 h) hNat

/-- The finite rank and excluded middle give the no-self-contained-borrowing
cut: the rank gives well-founded actual grounding, and the existing
equivalence (`borrowingEscapeWFEquivalence`, which needs excluded middle)
turns it into the cut. -/
theorem borrowingEscapeFromFiniteRank {W B : Type} (m : Profile W B) (w : W)
    (hRank : ActualGroundingFiniteRank m w) (hEM : ExcludedMiddle) :
    ActualConcreteBorrowingEscape m w := by
  have hWF : ActualGroundingWF m w := actualGroundingWFFromFiniteRank m w hRank
  exact (borrowingEscapeWFEquivalence W B m w hEM).2 hWF

/-- Global well-founded actual grounding restricts to the selected cone
(the cone is a subset of the actual concreta; `scopeComparison`). The strong
version is the only premise. -/
theorem selectedConeWFFromGlobalWF {W B : Type} (m : Profile W B) (w : W) (selected : B)
    (hWF : ActualGroundingWF m w) : ConeWellFounded m w selected :=
  (scopeComparison W B m w selected).1 hWF

/-- If the selected cone has no contingent root ancestor, then (with excluded
middle) every contingent cone member has an actual concrete ground: an
ungrounded one would be a contingent root ancestor. -/
theorem coneContingentGroundedFromNoContingentRoot {W B : Type} (m : Profile W B) (w : W)
    (selected : B) (hNo : NoContingentRootAncestor m w selected) (hEM : ExcludedMiddle) :
    ConeContingentGrounded m w selected := by
  intro x hCone hCont
  rcases hEM (∃ y, ActualConcreteGround m w y x) with hy | hNone
  · exact hy
  · exact absurd ⟨x, hCone, hCont, fun y hy => hNone ⟨y, hy⟩⟩ hNo

/-- Potency is capacity under privation, and privation in a capable subject
is lack of the act; hence potency is unactualized capacity. A chain through
the distinct middle term `Deprived`. -/
theorem potencyIsUnactualizedCapacityFromPrivation {Being Respect : Type}
    (InAct InPotency CanBe Deprived : Being → Respect → Prop)
    (hPriv : PotencyIsCapacityUnderPrivation InPotency CanBe Deprived)
    (hLack : PrivationIsLackOfActInCapable InAct CanBe Deprived) :
    PotencyIsUnactualizedCapacityReading InAct InPotency CanBe := by
  intro x r
  constructor
  · intro h
    obtain ⟨hc, hd⟩ := (hPriv x r).1 h
    exact ⟨hc, (hLack x r hc).1 hd⟩
  · rintro ⟨hc, hn⟩
    exact (hPriv x r).2 ⟨hc, (hLack x r hc).2 hn⟩

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
  intro x r
  constructor
  · intro h
    obtain ⟨hcap, ha⟩ := (hMoved x r).1 h
    exact ⟨(hPot x r).2 hcap, ha⟩
  · rintro ⟨hp, ha⟩
    exact (hMoved x r).2 ⟨(hPot x r).1 hp, ha⟩

/-! ## Controls -/

namespace Control
open TruthCore.Causality.Round3CogitoBase.Control

/-- A self-grounding element is not accessible. -/
theorem notAccOfSelf {α : Type} {r : α → α → Prop} {a : α} (h : r a a) : ¬ Acc r a := by
  intro hAcc
  have key : ∀ x, Acc r x → x = a → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hxa
      subst hxa
      exact ih x h rfl
  exact key a hAcc rfl

theorem doubtWithoutThought : DoubtWithoutThought :=
  ⟨⟨(), trivial, trivial⟩,
   fun h => by obtain ⟨_, he, _⟩ := h () trivial trivial; exact he,
   fun ⟨_, h⟩ => h,
   fun h => h () trivial trivial (fun ⟨_, h⟩ => h)⟩

theorem noPerformedDoubt : NoPerformedDoubt :=
  ⟨fun ⟨_, h, _⟩ => h, fun _ h _ => h.elim, fun ⟨_, h⟩ => h⟩

theorem nonAssentingThought : NonAssentingThought :=
  ⟨fun h => h () trivial, fun _ _ _ h => h, fun h => h () () trivial trivial⟩

theorem assentWithoutOpining : AssentWithoutOpining :=
  ⟨fun _ _ => trivial, fun h => h () () trivial trivial, fun h => h () () trivial trivial⟩

theorem selectedBearsNothing : SelectedBearsNothing :=
  ⟨fun ⟨_, h, _⟩ => h, fun _ _ h _ => h.elim, fun _ _ h _ => h.elim, fun h => h.1⟩

theorem abstractSelectedBearer : AbstractSelectedBearer :=
  ⟨⟨(), trivial, trivial⟩, fun h => h () () trivial trivial, fun _ _ _ _ => trivial,
   fun h => h.1⟩

theorem absentSelectedBearer : AbsentSelectedBearer :=
  ⟨⟨(), trivial, trivial⟩, fun _ _ _ _ => trivial, fun h => h () () trivial trivial,
   fun h => h.2⟩

theorem selfGroundingLoop : SelfGroundingLoop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨rank, h⟩
    exact Nat.lt_irrefl _ (h () () ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ trivial)
  · intro hWF
    exact notAccOfSelf (a := ⟨(), trivial, trivial⟩) trivial (hWF.apply _)
  · intro hWF
    exact notAccOfSelf
      (a := ⟨(), ⟨trivial, trivial⟩, Relation.ReflTransGen.refl⟩) trivial (hWF.apply _)
  · intro h
    rcases h Set.univ (fun _ _ => trivial) ⟨⟨(), trivial, trivial⟩, trivial⟩ with
        ⟨s, _, hs⟩ | ⟨g, _, _, hOut⟩
    · exact hs ⟨s, trivial⟩
    · exact hOut g.1 trivial trivial

theorem contingentRootCone : ContingentRootCone := by
  have hCone : TruthCore.Causality.SelectedAncestry.Cone contingentRootProfile true () () :=
    ⟨⟨trivial, rfl⟩, Relation.ReflTransGen.refl⟩
  have hCont : TruthCore.German.Kant.CosmologicalInference.ContingentAt
      contingentRootProfile.ontic true () :=
    ⟨rfl, false, trivial, Bool.noConfusion⟩
  refine ⟨fun h => h ⟨(), hCone, hCont, fun _ hy => hy.2.2⟩, fun h => ?_⟩
  obtain ⟨_, _, _, hg⟩ := h () hCone hCont
  exact hg

theorem capacityWithoutPotency : CapacityWithoutPotency :=
  ⟨fun h => (h () ()).2 ⟨trivial, trivial⟩,
   fun _ _ _ => ⟨fun _ h => h, fun _ => trivial⟩,
   fun h => (h () ()).2 ⟨trivial, fun h => h⟩⟩

theorem privationWithAct : PrivationWithAct :=
  ⟨fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩,
   fun h => (h () () trivial).1 trivial trivial,
   fun h => ((h () ()).1 trivial).2 trivial⟩

theorem motionWithoutCapacity : MotionWithoutCapacity :=
  ⟨fun h => ((h () ()).1 trivial).2,
   fun _ _ => ⟨fun h => h.elim, fun h => h.1⟩,
   fun h => ((h () ()).1 trivial).1⟩

theorem capacityNotPotency : CapacityNotPotency :=
  ⟨fun _ _ => ⟨fun _ => ⟨⟨trivial, fun h => h⟩, trivial⟩, fun _ => trivial⟩,
   fun h => (h () ()).2 ⟨trivial, fun h => h⟩,
   fun h => ((h () ()).1 trivial).1⟩

theorem cogitoWitness : CogitoWitness :=
  ⟨⟨(), trivial, trivial⟩, fun _ _ _ => ⟨(), trivial, trivial⟩, ⟨(), trivial⟩,
   fun _ _ _ h => h ⟨(), trivial⟩, fun _ _ => trivial, fun _ _ _ _ => trivial,
   fun _ _ _ _ => trivial, ⟨(), trivial, trivial⟩, fun _ _ _ _ => trivial,
   fun _ _ _ _ => trivial, ⟨trivial, trivial⟩⟩

theorem groundingWitness : GroundingWitness := by
  have hRank : ActualGroundingFiniteRank rootedProfile true := by
    refine ⟨Bool.toNat, ?_⟩
    rintro x y - - ⟨rfl, rfl⟩
    exact Nat.zero_lt_one
  have hWF := actualGroundingWFFromFiniteRank rootedProfile true hRank
  refine ⟨hRank, hWF, selectedConeWFFromGlobalWF rootedProfile true true hWF, ?_, ?_, ⟨rfl, rfl⟩⟩
  · rintro ⟨x, _, hCont, hNoGround⟩
    cases x with
    | true => exact hNoGround false ⟨trivial, Or.inl rfl, rfl, rfl⟩
    | false =>
      obtain ⟨_, _, _, hv⟩ := hCont
      exact hv (Or.inl rfl)
  · intro x _ hCont
    cases x with
    | true => exact ⟨false, trivial, Or.inl rfl, rfl, rfl⟩
    | false =>
      obtain ⟨_, _, _, hv⟩ := hCont
      exact (hv (Or.inl rfl)).elim

theorem potencyWitness : PotencyWitness :=
  ⟨fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩,
   fun _ _ _ => ⟨fun _ h => h, fun _ => trivial⟩,
   fun _ _ => ⟨fun _ => ⟨trivial, fun h => h⟩, fun _ => trivial⟩,
   fun _ _ => ⟨fun _ => ⟨⟨trivial, fun h => h⟩, trivial⟩, fun _ => trivial⟩,
   fun _ _ => ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩⟩

end Control

/-- Omission models for every load-bearing premise other than excluded middle,
and joint nonvacuity witnesses for the three vocabularies. -/
theorem controls : TruthCore.Causality.Round3CogitoBase.Control.Certificate :=
  ⟨Control.doubtWithoutThought, Control.noPerformedDoubt, Control.nonAssentingThought,
   Control.assentWithoutOpining, Control.selectedBearsNothing, Control.abstractSelectedBearer,
   Control.absentSelectedBearer, Control.selfGroundingLoop, Control.contingentRootCone,
   Control.capacityWithoutPotency, Control.privationWithAct, Control.motionWithoutCapacity,
   Control.capacityNotPotency, Control.cogitoWitness, Control.groundingWitness,
   Control.potencyWitness⟩

end TruthCore.Results.Causality.Round3CogitoBase
