import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3Interpretation
import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution

/-!
Finite models for the two readings of the *prima via* per se premise.

* `strongModel`: `g` (moved in no respect) moves `f` in respect `other`; `f`
  moves `x` in respect `heat`. `f` is a per se link (it is moved), the series
  ends at `g`, and `f` is moved only in a respect irrelevant to heating `x`.
  All strong premises hold and the irrelevant-respect objection's situation obtains.
* `weakModel`: `f` heats `x`; `g` moves `f` in `other`; `f` moves `g` in
  `other2`. No being-moved is relevant to any moving, so there are no per se
  links. All weak premises hold, yet every being is moved: there is no mover
  moved by none.

The proofs use only case analysis, so they need no axioms.
-/

namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
open TruthCore.Latin.Aquinas.SummaTheologiae

inductive StrongBeing | g | f | x
inductive StrongRespect | heat | other

/- The finite predicates are written as nested, non-overlapping matches: an
overlapping catch-all pattern would make the definitions depend on `propext`. -/

def strongHeat : StrongRespect → Prop
  | .heat => True
  | .other => False

def strongOther : StrongRespect → Prop
  | .heat => False
  | .other => True

def strongMovedIn : StrongBeing → StrongRespect → Prop
  | .g, _ => False
  | .f, r => strongOther r
  | .x, r => strongHeat r

def strongMovesIn : StrongBeing → StrongBeing → StrongRespect → Prop
  | .g, b, r => match b with
    | .f => strongOther r
    | .g => False
    | .x => False
  | .f, b, r => match b with
    | .x => strongHeat r
    | .f => False
    | .g => False
  | .x, _, _ => False

def strongInAct : StrongBeing → StrongRespect → Prop
  | .g, r => strongOther r
  | .f, r => strongHeat r
  | .x, _ => False

def strongMovesAsMoved : StrongBeing → StrongBeing → Prop
  | .f, b => match b with
    | .x => True
    | .f => False
    | .g => False
  | .g, _ => False
  | .x, _ => False

def strongModel : MotionModel where
  Being := StrongBeing
  Respect := StrongRespect
  MovedIn := strongMovedIn
  MovesIn := strongMovesIn
  InPotency := strongMovedIn
  InAct := strongInAct
  MovesAsMoved := strongMovesAsMoved
  RelevantTo := fun _ _ _ _ => False

theorem strongModel_acc : ∀ b, Acc strongMovesAsMoved b := by
  have hf : Acc strongMovesAsMoved .f :=
    Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hg : Acc strongMovesAsMoved .g :=
    Acc.intro _ fun a h => by cases a <;> exact False.elim h
  intro b
  cases b with
  | g => exact hg
  | f => exact hf
  | x =>
    exact Acc.intro _ fun a h => by
      cases a with
      | f => exact hf
      | g => exact False.elim h
      | x => exact False.elim h

theorem strongModel_premises : StrongPremises strongModel := by
  refine ⟨⟨.x, .heat, trivial⟩, fun _ _ h => h, ?_, ?_, ?_, ?_, strongModel_acc⟩
  · intro a b r h
    cases a <;> cases b <;> cases r <;> first | exact False.elim h | exact trivial
  · intro b r h
    cases b <;> cases r
    all_goals first
      | exact False.elim h
      | exact ⟨.f, trivial⟩
      | exact ⟨.g, trivial⟩
  · intro b r h
    cases b <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2
  · intro a b r _ h ⟨r', hMoved⟩
    cases a <;> cases b <;> cases r
    all_goals first
      | exact False.elim h
      | exact trivial
      | (cases r' <;> exact False.elim hMoved)

theorem strongModel_objection : IrrelevantRespectObjection strongModel :=
  ⟨.f, .x, .heat, .other, trivial, fun _ h => h.2, trivial⟩

inductive WeakBeing | f | g | x
inductive WeakRespect | heat | other | other2

def weakHeat : WeakRespect → Prop
  | .heat => True
  | .other => False
  | .other2 => False

def weakOther : WeakRespect → Prop
  | .heat => False
  | .other => True
  | .other2 => False

def weakOther2 : WeakRespect → Prop
  | .heat => False
  | .other => False
  | .other2 => True

def weakMovedIn : WeakBeing → WeakRespect → Prop
  | .x, r => weakHeat r
  | .f, r => weakOther r
  | .g, r => weakOther2 r

def weakMovesIn : WeakBeing → WeakBeing → WeakRespect → Prop
  | .f, b, r => match b with
    | .x => weakHeat r
    | .g => weakOther2 r
    | .f => False
  | .g, b, r => match b with
    | .f => weakOther r
    | .g => False
    | .x => False
  | .x, _, _ => False

def weakInAct : WeakBeing → WeakRespect → Prop
  | .f, r => match r with
    | .heat => True
    | .other => False
    | .other2 => True
  | .g, r => weakOther r
  | .x, _ => False

def weakModel : MotionModel where
  Being := WeakBeing
  Respect := WeakRespect
  MovedIn := weakMovedIn
  MovesIn := weakMovesIn
  InPotency := weakMovedIn
  InAct := weakInAct
  MovesAsMoved := fun _ _ => False
  RelevantTo := fun _ _ _ _ => False

theorem weakModel_premises : WeakPremises weakModel := by
  refine ⟨⟨.x, .heat, trivial⟩, fun _ _ h => h, ?_, ?_, ?_,
    fun _ _ _ _ _ _ _ hRelevant => hRelevant,
    fun _ => Acc.intro _ fun _ h => False.elim h⟩
  · intro a b r h
    cases a <;> cases b <;> cases r <;> first | exact False.elim h | exact trivial
  · intro b r h
    cases b <;> cases r
    all_goals first
      | exact False.elim h
      | exact ⟨.f, trivial⟩
      | exact ⟨.g, trivial⟩
  · intro b r h
    cases b <;> cases r <;> first | exact False.elim h.1 | exact False.elim h.2

theorem weakModel_objection : IrrelevantRespectObjection weakModel :=
  ⟨.f, .x, .heat, .other, trivial, fun _ h => h.2, trivial⟩

theorem weakModel_no_unmoved_mover : ¬ AbsoluteConclusion weakModel := by
  intro h
  apply h
  intro ⟨b, _, hUnmoved⟩
  cases b with
  | f => exact hUnmoved .other trivial
  | g => exact hUnmoved .other2 trivial
  | x => exact hUnmoved .heat trivial

/-- The strong reading yields *a nullo movetur* in every model. -/
theorem strongReadingYields : StrongReadingYieldsUnmovedMover := by
  intro M ⟨hSense, hPotency, hAct, hReduction, hNotBoth, hPerSe, hRegress⟩
  exact PrimaVia.primaVia M.MovedIn M.MovesIn M.InPotency M.InAct M.MovesAsMoved
    hSense hPotency hAct hReduction hNotBoth hPerSe hRegress

/-- The weaker reading does not yield *a nullo movetur* in every model. -/
theorem weakReadingDoesNotYield : WeakReadingDoesNotYieldUnmovedMover :=
  fun h => weakModel_no_unmoved_mover (h weakModel weakModel_premises)

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaModels
