module
public import TruthCore.Causality.WitnessLocalTeleology
@[expose] public section
namespace TruthCore.Results.Causality.WitnessLocalTeleology
open TruthCore.Causality.WitnessLocalTeleology
open TruthCore.Causality.TeleologyFirstMover.Control hiding Controls
open TruthCore.Latin.Aquinas.SummaTheologiae TruthCore.Case.Catholicism
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
theorem weaken {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop)
    (h : Universal Moved Moves Body Cog Intel Reg Best Chance Tends Dir) :
    Bundle Moved Moves Body Cog Intel Reg Best Chance Tends Dir := by
  obtain ⟨hl, ho, hn, hd, ha, hr, hm⟩ := h
  obtain ⟨x, hx⟩ := ho.1
  obtain ⟨e, he, hb⟩ := ho.2 x hx
  exact ⟨x, e, hl x hx, ⟨hx, he, hb⟩, hn x e, hd x e, ha x e,
    fun d => hr d x e, fun d => hm d x e⟩

theorem firstMover {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop)
    (h : Bundle Moved Moves Body Cog Intel Reg Best Chance Tends Dir) :
    ThereIsAFirstUnmovedMover Moved Moves := by
  obtain ⟨x, e, hl, ⟨hx, he, hb⟩, hn, hd, ha, hr, hm⟩ := h
  have ht : Tends x e := (hd he hb).resolve_left (hn he)
  obtain ⟨d, _, _, hdir⟩ := ha hl ht
  obtain ⟨f, _, _, hu, hf⟩ := hr d hx hdir
  obtain ⟨r, hmove⟩ := hm f hf
  exact ⟨f, ⟨⟨x, r, hmove⟩, hu⟩⟩
theorem pack {Being : Type} {Respect : Type} {End : Type}
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
    Universal MovedIn MovesIn NaturalBody HasCognition Intelligent RegularlyAttains Best ByChance TendsTo Directs := by
  exact ⟨hLack, hObs, hNotChance, hDich, hArrow, hReduce, hMoving⟩

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
theorem controls : TruthCore.Causality.WitnessLocalTeleology.Controls := by
  dsimp only [TruthCore.Causality.WitnessLocalTeleology.Controls, Bundle, LocalExcept, Universal,
    strict, flat, base, noReduction, noMoving,
    NaturalBodiesLackCognitionReading, NaturalBodiesActRegularlyForTheBestReading,
    RegularityIsNotByChanceReading, RegularBestByChanceOrByIntentionReading,
    NonCognitiveTendingNeedsKnowingDirectorReading,
    NaturalDirectionReducedToIntelligentImmobileDirector, DirectingIsMoving,
    ThereIsAFirstUnmovedMover, IsFirstUnmovedMover,
    nothingMoved, noMoves, noneP, allEnd, noEnd, noDirects, isBody, isDirector,
    isB0, isB1, bodyEnd, oneDirects, twoDirects, directorsMoved]
  repeat' apply And.intro
  all_goals decide
end TruthCore.Results.Causality.WitnessLocalTeleology
