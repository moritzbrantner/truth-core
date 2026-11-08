module
public import TruthCore.Causality.TeleologyFirstMover

@[expose] public section
namespace TruthCore.Results.Causality.TeleologyFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Results.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
open TruthCore.Causality.TeleologyFirstMover.Control

theorem firstMover {Being : Type} {Respect : Type} {End : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (NaturalBody HasCognition Intelligent : Being → Prop)
    (RegularlyAttains Best ByChance TendsTo : Being → End → Prop)
    (Directs : Being → Being → End → Prop)
    (hLack : NaturalBodiesLackCognitionReading NaturalBody HasCognition)
    (hObs : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best)
    (hNotChance : RegularityIsNotByChanceReading RegularlyAttains ByChance)
    (hDich : RegularBestByChanceOrByIntentionReading RegularlyAttains Best ByChance TendsTo)
    (hArrow : NonCognitiveTendingNeedsKnowingDirectorReading HasCognition Intelligent
      TendsTo Directs)
    (hReduce : NaturalDirectionReducedToIntelligentImmobileDirector MovedIn NaturalBody
      HasCognition Intelligent Directs)
    (hMoving : DirectingIsMoving MovesIn Directs)
 :
    ThereIsAFirstUnmovedMover MovedIn MovesIn := by
  have hEach := QuintaViaEachDirected.eachDirected NaturalBody HasCognition Intelligent
    RegularlyAttains Best ByChance TendsTo Directs hLack hObs hNotChance hDich hArrow
  obtain ⟨x, hx⟩ := hObs.1
  obtain ⟨e, _, d, _, _, hd⟩ := hEach x hx
  obtain ⟨f, _, _, hUnmoved, hDirects⟩ := hReduce d x e hx hd
  obtain ⟨r, hMoves⟩ := hMoving f x e hDirects
  exact ⟨f, ⟨⟨x, r, hMoves⟩, hUnmoved⟩⟩

theorem governorProjects {B R E : Type} (Moved : B → R → Prop)
    (Moves : B → B → R → Prop) (Body Intelligent : B → Prop)
    (Directs : B → B → E → Prop)
    (h : OneIntelligentFirstMoverGovernsNature Moved Moves Body Intelligent Directs) :
    ThereIsAFirstUnmovedMover Moved Moves := by
  obtain ⟨f, hFirst, _, _⟩ := h
  exact ⟨f, hFirst⟩

private theorem forallW {P : W → Prop} :
    (∀ x, P x) ↔ P .b0 ∧ P .b1 ∧ P .d0 ∧ P .d1 := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h0, h1, h2, h3⟩ x
    cases x <;> assumption

private theorem existsW {P : W → Prop} :
    (∃ x, P x) ↔ P .b0 ∨ P .b1 ∨ P .d0 ∨ P .d1 := by
  constructor
  · rintro ⟨x, h⟩
    cases x with
    | b0 => exact Or.inl h
    | b1 => exact Or.inr (Or.inl h)
    | d0 => exact Or.inr (Or.inr (Or.inl h))
    | d1 => exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact ⟨.b0, h⟩
    · exact ⟨.b1, h⟩
    · exact ⟨.d0, h⟩
    · exact ⟨.d1, h⟩

deriving instance DecidableEq for W

private instance forallDecidable {P : W → Prop} [Decidable (P .b0)] [Decidable (P .b1)]
    [Decidable (P .d0)] [Decidable (P .d1)] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (P .b0 ∧ P .b1 ∧ P .d0 ∧ P .d1) forallW.symm

private instance existsDecidable {P : W → Prop} [Decidable (P .b0)] [Decidable (P .b1)]
    [Decidable (P .d0)] [Decidable (P .d1)] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (P .b0 ∨ P .b1 ∨ P .d0 ∨ P .d1) existsW.symm

private instance forallUnitDecidable {P : Unit → Prop} [Decidable (P ())] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (P ()) ⟨fun h x => by cases x; exact h, fun h => h ()⟩

private instance existsUnitDecidable {P : Unit → Prop} [Decidable (P ())] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (P ()) ⟨fun h => ⟨(), h⟩, fun ⟨x, h⟩ => by cases x; exact h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem controls : Controls := by
  dsimp only [Controls, Omits, AllExcept, flat, base, noReduction, noMoving,
    NaturalBodiesLackCognitionReading, NaturalBodiesActRegularlyForTheBestReading,
    RegularityIsNotByChanceReading, RegularBestByChanceOrByIntentionReading,
    NonCognitiveTendingNeedsKnowingDirectorReading,
    NaturalDirectionReducedToIntelligentImmobileDirector, DirectingIsMoving,
    ThereIsAFirstUnmovedMover, IsFirstUnmovedMover, AtMostOneFirstUnmovedMover,
    nothingMoved, noMoves, noneP, allEnd, noEnd, noDirects, isBody, isDirector,
    isB0, isB1, bodyEnd, oneDirects, twoDirects, directorsMoved]
  repeat' apply And.intro
  all_goals decide
end TruthCore.Results.Causality.TeleologyFirstMover
