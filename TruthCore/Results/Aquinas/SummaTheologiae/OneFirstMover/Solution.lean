import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question11.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Case.Catholicism.StageOneBridges
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  FirstUnmovedMoverHasEveryPerfection FirstUnmovedMoversIdenticalOrDistinct
  FirstUnmovedMoverIsFirstBeing)

/-- ST I q.11 a.3 co., second proof, for the *prima via*'s mover. If there were
two first movers moved by none, they would differ in some act: one in act in a
respect in which the other is not. Then the other would lack a perfection, but
each has every perfection (open bridge). So two first movers are not distinct,
and, given that they are either the same or distinct, they are the same.
Discharges the #159 gap statement `AtMostOneFirstUnmovedMover`. -/
theorem oneFirstMover {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (hPerfect : FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct)
    (hDiffer : PluralFirstMoversWouldDifferInActReading MovedIn MovesIn InAct)
    (hEither : FirstUnmovedMoversIdenticalOrDistinct MovedIn MovesIn) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  intro f g hF hG
  -- INF-AQUINAS-ST-I-Q11-A3-NO-TWO-FIRST-MOVERS: reductio of plurality
  have hNotDistinct : ¬ f ≠ g := by
    intro hDistinct
    obtain ⟨r, hDiff⟩ := hDiffer f g hF hG hDistinct
    cases hDiff with
    | inl h => exact h.2 (hPerfect g hG r)
    | inr h => exact h.2 (hPerfect f hF r)
  -- INF-AQUINAS-ST-I-Q11-A3-ONE-FIRST-MOVER: same or distinct, so the same
  cases hEither f g hF hG with
  | inl hSame => exact hSame
  | inr hDistinct => exact absurd hDistinct hNotDistinct

namespace Joint

/-- `g` moves `f` in `other`; `f`, so moved, moves `x` in `heat` (a per se link).
`f` and `x` are bodies; `f` is composite, composed of matter and form, with an
esse other than its essence, and has the component `c`. -/
inductive B | g | f | x | c
inductive R | heat | other

def heat : R → Prop
  | .heat => True
  | .other => False

def other : R → Prop
  | .heat => False
  | .other => True

def movedIn : B → R → Prop
  | .f, r => other r
  | .x, r => heat r
  | .g, _ => False
  | .c, _ => False

def movesIn : B → B → R → Prop
  | .g, b, r => match b with
    | .f => other r
    | .g => False
    | .x => False
    | .c => False
  | .f, b, r => match b with
    | .x => heat r
    | .g => False
    | .f => False
    | .c => False
  | .x, _, _ => False
  | .c, _, _ => False

def inAct : B → R → Prop
  | .g, _ => True
  | .f, r => heat r
  | .x, _ => False
  | .c, _ => False

def isF : B → Prop
  | .f => True
  | .g => False
  | .x => False
  | .c => False

def isFOrX : B → Prop
  | .f => True
  | .x => True
  | .g => False
  | .c => False

def movesAsMoved : B → B → Prop
  | .f, b => match b with
    | .x => True
    | .g => False
    | .f => False
    | .c => False
  | .g, _ => False
  | .x, _ => False
  | .c, _ => False

def priorSimply : B → B → Prop
  | .g, b => isF b
  | .c, b => isF b
  | .f, b => match b with
    | .x => True
    | .g => False
    | .f => False
    | .c => False
  | .x, _ => False

def componentOf : B → B → Prop
  | .c, b => isF b
  | .g, _ => False
  | .f, _ => False
  | .x, _ => False

def essenceOf : B → Bool
  | .f => false
  | .g => true
  | .x => true
  | .c => true

def esseOf : B → Bool := fun _ => true

theorem acc : ∀ b, Acc movesAsMoved b := by
  have hf : Acc movesAsMoved .f :=
    Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hg : Acc movesAsMoved .g :=
    Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hc : Acc movesAsMoved .c :=
    Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hx : Acc movesAsMoved .x :=
    Acc.intro _ fun a h => by
      cases a
      · exact False.elim h
      · exact hf
      · exact False.elim h
      · exact False.elim h
  intro b
  cases b
  · exact hg
  · exact hf
  · exact hx
  · exact hc

end Joint

/-- The *prima via*'s premises (#151) and every premise of the #165 results hold
together in one finite model, so none of the results follows from inconsistent
premises. The model also witnesses a per se link, a moving body, a composite with
a component, matter-form composition and an esse other than an essence, so those
premises are not satisfied only through false antecedents.

`PluralFirstMoversWouldDifferInActReading` holds only vacuously here, as it must
in any model of all the premises: with every perfection it rules out two first
movers. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Principle : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply ComponentOf : Being → Being → Prop)
      (Body ComposedOfMatterAndForm Composite : Being → Prop)
      (essenceOf esseOf : Being → Principle),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply ∧
      NoBodyMovesUnlessMovedReading MovedIn MovesIn Body ∧
      CompositePosteriorToComponentsReading ComponentOf PriorSimply ∧
      CompositeHasComponentOtherThanItselfReading Composite ComponentOf ∧
      MatterFormAndEsseEssenceAreCompositionsReading
        ComposedOfMatterAndForm Composite essenceOf esseOf ∧
      FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct ∧
      PluralFirstMoversWouldDifferInActReading MovedIn MovesIn InAct ∧
      FirstUnmovedMoversIdenticalOrDistinct MovedIn MovesIn ∧
      (∃ y x, MovesAsMoved y x) ∧
      (∃ b x r, Body b ∧ MovesIn b x r) ∧
      (∃ b p, ComposedOfMatterAndForm b ∧ ComponentOf p b ∧ esseOf b ≠ essenceOf b) := by
  open Joint in
  refine ⟨B, R, Bool, movedIn, movesIn, movedIn, inAct, movesAsMoved, priorSimply,
    componentOf, isFOrX, isF, isF, essenceOf, esseOf, ?_⟩
  -- the only first mover moved by none is `g`
  have hOnlyG : ∀ b, IsFirstUnmovedMover movedIn movesIn b → b = .g := by
    intro b ⟨⟨y, r, hm⟩, hu⟩
    cases b
    · rfl
    · exact False.elim (hu .other trivial)
    · exact False.elim hm
    · exact False.elim hm
  refine ⟨⟨.x, .heat, trivial⟩, ?_, ?_, ?_, ?_, ?_, acc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨.f, .x, trivial⟩, ⟨.f, .x, .heat, trivial, trivial⟩,
    ⟨.f, .c, trivial, trivial, Bool.noConfusion⟩⟩
  · exact fun _ _ h => h
  · intro y b r hm
    cases y <;> cases b <;> cases r
    all_goals first | exact trivial | exact False.elim hm
  · intro b r hm
    cases b <;> cases r
    all_goals first
      | exact False.elim hm
      | exact ⟨.g, trivial⟩
      | exact ⟨.f, trivial⟩
  · intro b r ⟨ha, hp⟩
    cases b <;> cases r
    all_goals first | exact False.elim ha | exact False.elim hp
  · intro y b r _ hmv ⟨r', hm⟩
    cases y <;> cases b <;> cases r <;> cases r'
    all_goals first | exact trivial | exact False.elim hmv | exact False.elim hm
  · intro b r hp
    cases b <;> cases r
    all_goals first
      | exact False.elim hp
      | exact ⟨.g, trivial, trivial⟩
      | exact ⟨.f, trivial, trivial⟩
  · intro b hb y hy
    have hg := hOnlyG b hb
    subst hg
    cases y <;> first | rfl | exact False.elim hy
  · intro b hb ⟨y, r, hm⟩
    cases b
    · exact False.elim hb
    · exact ⟨.other, trivial⟩
    · exact False.elim hm
    · exact False.elim hb
  · intro p b h
    cases p <;> cases b <;> first | exact trivial | exact False.elim h
  · intro b hb
    cases b
    · exact False.elim hb
    · exact ⟨.c, trivial, B.noConfusion⟩
    · exact False.elim hb
    · exact False.elim hb
  · intro b
    cases b
    · exact ⟨False.elim, fun h => False.elim (h rfl)⟩
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · exact ⟨False.elim, fun h => False.elim (h rfl)⟩
    · exact ⟨False.elim, fun h => False.elim (h rfl)⟩
  · intro b hb r
    have hg := hOnlyG b hb
    subst hg
    exact trivial
  · intro f' g' hf hg hne
    exact False.elim (hne ((hOnlyG f' hf).trans (hOnlyG g' hg).symm))
  · intro f' g' _ _
    exact Or.inl ((hOnlyG f' ‹_›).trans (hOnlyG g' ‹_›).symm)
end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
