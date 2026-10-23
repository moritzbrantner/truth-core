import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question11.Article3
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.FirstMoverAttributes
import TruthCore.Case.Catholicism.StageOne
namespace TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (AtMostOneFirstUnmovedMover IsFirstUnmovedMover
  FirstUnmovedMoverIsPureAct)

/-- ST I q.11 a.3 co., second proof, for the *prima via*'s mover: two first
movers moved by none would each have every perfection, so they would agree in
every act, and beings that agree in every act are one. Discharges the #159 gap
statement `AtMostOneFirstUnmovedMover`. -/
theorem oneFirstMover {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (hPerfect : FirstUnmovedMoverHasEveryPerfectionReading MovedIn MovesIn InAct)
    (hDiffer : ManyMustDifferReading InAct) :
    AtMostOneFirstUnmovedMover MovedIn MovesIn := by
  -- INF-AQUINAS-ST-I-Q11-A3-ONE-FIRST-MOVER
  intro f g hF hG
  apply hDiffer f g
  intro r
  -- Whatever belongs to one in act belongs to the other: each has every act.
  exact ⟨fun _ => hPerfect g hG r, fun _ => hPerfect f hF r⟩

namespace Joint

inductive B | f | x
inductive R | heat

def movedIn : B → R → Prop
  | .x, _ => True
  | .f, _ => False

def movesIn : B → B → R → Prop
  | .f, b, _ => match b with
    | .x => True
    | .f => False
  | .x, _, _ => False

/-- `x` alone is in potency, so it is also the only body, composite, and thing
composed of matter and form. -/
def onlyX : B → Prop
  | .x => True
  | .f => False

def inPotency : B → R → Prop := fun b _ => onlyX b

def inAct : B → R → Prop
  | .f, _ => True
  | .x, _ => False

def priorSimply : B → B → Prop
  | .f, b => onlyX b
  | .x, _ => False

def essenceOf : B → Bool
  | .f => true
  | .x => false

def esseOf : B → Bool := fun _ => true

end Joint

/-- The premises of the #165 results are jointly satisfiable with the *prima
via*'s premises (#151), in a model where they are not all vacuous: `f` moves
`x`; `x` is moved, in potency, a body, composite, composed of matter and form,
simply posterior to `f`, and has an esse other than its essence. So none of the
results follows from inconsistent premises. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect Principle : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (Body ComposedOfMatterAndForm Composite : Being → Prop)
      (essenceOf esseOf : Being → Principle),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      NoBodyMovesUnlessMovedReading MovedIn MovesIn Body ∧
      FirstUnmovedMoverIsFirstBeingReading MovedIn MovesIn PriorSimply ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      MatterIsInPotencyReading InPotency ComposedOfMatterAndForm ∧
      EsseOtherThanEssenceIsPotencyReading InPotency essenceOf esseOf ∧
      CompositeIsInPotencyReading InPotency Composite ∧
      FirstUnmovedMoverHasEveryPerfectionReading MovedIn MovesIn InAct ∧
      ManyMustDifferReading InAct ∧
      (∃ b, Body b ∧ ComposedOfMatterAndForm b ∧ Composite b ∧ esseOf b ≠ essenceOf b) := by
  open Joint in
  refine ⟨B, R, Bool, movedIn, movesIn, inPotency, inAct, fun _ _ => False, priorSimply,
    onlyX, onlyX, onlyX, essenceOf, esseOf, ?_⟩
  refine ⟨⟨.x, .heat, trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b r hm; cases b <;> first | exact hm | exact False.elim hm
  · intro y b r hm; cases y <;> cases b <;> first | exact trivial | exact False.elim hm
  · intro b r hm; cases b
    · exact False.elim hm
    · exact ⟨.f, trivial⟩
  · intro b r ⟨ha, hp⟩; cases b <;> first | exact False.elim ha | exact False.elim hp
  · intro y b r _ hmv ⟨r', hm⟩
    cases y <;> cases b <;> first | exact False.elim hmv | exact False.elim hm
  · intro b; exact Acc.intro _ fun _ h => False.elim h
  · intro b hb ⟨y, r, hm⟩; cases b <;> first | exact False.elim hb | exact False.elim hm
  · intro b hb y hy
    cases b
    · cases y
      · rfl
      · exact False.elim hy
    · exact False.elim (hb.2 .heat trivial)
  · intro b r hp; cases b
    · exact False.elim hp
    · exact ⟨.f, trivial, trivial⟩
  · intro b hb; exact ⟨.heat, hb⟩
  · intro b hb; cases b
    · exact False.elim (hb rfl)
    · exact ⟨.heat, trivial⟩
  · intro b hb; exact ⟨.heat, hb⟩
  · intro b hb r; cases b
    · exact trivial
    · obtain ⟨y, r', hm⟩ := hb.1; exact False.elim hm
  · intro b c h
    cases b <;> cases c
    · rfl
    · exact False.elim ((h .heat).1 trivial)
    · exact False.elim ((h .heat).2 trivial)
    · rfl
  · exact ⟨.x, trivial, trivial, trivial, Bool.noConfusion⟩
end TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover
