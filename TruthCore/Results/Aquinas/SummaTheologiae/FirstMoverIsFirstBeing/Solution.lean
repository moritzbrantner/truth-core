import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
import TruthCore.Greek.Aristotle.Metaphysics
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (PriorAsCauseIsMoreInBeingReading)
open TruthCore.Case.Catholicism (FirstUnmovedMoverIsFirstBeing IsFirstUnmovedMover)

/-- The first-being bridge of #166, derived through the *quarta via*. Something
`m` is maximal in being and causes the being of all others (`quartaVia`). Nothing
is simply prior to `m`, since what is simply prior is more in being
(*Metaphysics* II.1) and nothing is more in being than `m`. Every first mover
moved by none is `m` (`firstMoverIsMaximeEns`), so it is the first being. -/
theorem firstMoverIsFirstBeing {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn)
    (hInAct : MovesOnlyAsInActReading MovesIn InAct)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hApplied : CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse)
    (hPriorMore : PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUARTA-VIA (result AQUINAS-ST-I-Q2-A3-QUARTA-VIA)
  obtain ⟨m, hMax, _⟩ := QuartaVia.quartaVia InAct MoreIn CausesIn bonum verum nobile
    esse hGrades hApproach hTrue hGenus
  -- INF-AQUINAS-FIRST-MOVER-IS-FIRST-BEING: what is simply prior is more in being,
  -- so nothing is simply prior to m
  have hFirst : IsFirstBeing PriorSimply m := by
    intro y hPrior
    exact absurd (hPriorMore y m hPrior) (hMax.2 y)
  -- INF-AQUINAS-FIRST-MOVER-IS-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS)
  have hIdent := FirstMoverIsMaximeEns.firstMoverIsMaximeEns MovedIn MovesIn InAct
    MoreIn CausesIn esse hGenus hInAct hBeing hApplied hEM
  -- every first mover moved by none is m, hence the first being
  intro f hF
  rw [hIdent f hF m hMax]
  exact hFirst

namespace Intelligence

/-! `m` causes the being of everything else; `f` heats `x` and is moved by none,
like a separate intelligence of Aristotle's moving its sphere without being moved;
its being is caused by `m`, and it is not applied to act by `m`. -/

inductive B | m | f | x
inductive R | esse | heat

def more : B → B → Prop
  | .m, .m => False
  | .m, .f => True
  | .m, .x => True
  | .f, .m => False
  | .f, .f => False
  | .f, .x => True
  | .x, .m => False
  | .x, .f => False
  | .x, .x => False

def inAct : B → R → Prop
  | .m, .esse => True
  | .m, .heat => True
  | .f, .esse => True
  | .f, .heat => True
  | .x, .esse => True
  | .x, .heat => False

def inPotency : B → R → Prop
  | .m, .esse => False
  | .m, .heat => False
  | .f, .esse => False
  | .f, .heat => False
  | .x, .esse => False
  | .x, .heat => True

def movesIn : B → B → R → Prop
  | .m, .m, .esse => False
  | .m, .m, .heat => False
  | .m, .f, .esse => False
  | .m, .f, .heat => False
  | .m, .x, .esse => False
  | .m, .x, .heat => False
  | .f, .m, .esse => False
  | .f, .m, .heat => False
  | .f, .f, .esse => False
  | .f, .f, .heat => False
  | .f, .x, .esse => False
  | .f, .x, .heat => True
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .f, .esse => False
  | .x, .f, .heat => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False

def causesIn : B → B → R → Prop
  | .m, .m, .esse => True
  | .m, .m, .heat => True
  | .m, .f, .esse => True
  | .m, .f, .heat => True
  | .m, .x, .esse => True
  | .m, .x, .heat => True
  | .f, .m, .esse => False
  | .f, .m, .heat => False
  | .f, .f, .esse => False
  | .f, .f, .heat => False
  | .f, .x, .esse => False
  | .f, .x, .heat => False
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .f, .esse => False
  | .x, .f, .heat => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False

end Intelligence

/-- Without the q.105 a.5 premise the bridge fails. In `Intelligence` every other
premise of `firstMoverIsFirstBeing` holds, with excluded middle in the only form
the proof uses (identity of beings, decidable in the model), and so do the seven
*prima via* premises and act's simple priority; but the first mover moved by none
`f` is caused by `m`, which is simply prior to it. So the *quarta via* alone does
not reach the *prima via*'s mover: an unmoved mover caused in its being is
possible unless such agents are moved to act. -/
theorem withoutAppliedAgentNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  open Intelligence in
  intro h
  have hB := h B R inPotency movesIn inPotency inAct (fun _ _ => False) more
    (fun _ => more) causesIn .esse .esse .esse .esse
    ⟨.x, .heat, trivial⟩
    (fun _ _ hm => hm)
    (by intro y b r hm; cases y <;> cases b <;> cases r <;> first | exact True.intro | exact False.elim hm)
    (by
      intro b r hm
      cases b <;> cases r
      all_goals first | exact False.elim hm | exact ⟨.f, trivial⟩)
    (by intro b r ⟨ha, hp⟩; cases b <;> cases r <;> first | exact False.elim ha | exact False.elim hp)
    (by
      intro a b r _ hmv ⟨r', hm⟩
      cases a <;> cases b <;> cases r <;> cases r'
      all_goals first | exact False.elim hmv | exact False.elim hm)
    (fun _ => Acc.intro _ fun _ h => False.elim h)
    (by
      intro b r hp
      cases b <;> cases r
      all_goals first | exact False.elim hp | exact ⟨.f, trivial, trivial⟩)
    ⟨⟨.m, .f, trivial⟩, ⟨.m, .f, trivial⟩, ⟨.m, .f, trivial⟩⟩
    (by
      intro r _
      refine ⟨.m, by cases r <;> exact True.intro, fun y hy => ?_⟩
      cases y <;> exact hy)
    (fun _ hm => hm)
    (by
      intro r b ⟨_, hNo⟩ y _ _
      cases b
      · cases y <;> cases r <;> exact True.intro
      · exact (hNo .m trivial).elim
      · exact (hNo .m trivial).elim)
    (by intro b r _; cases b <;> exact True.intro)
    (fun _ _ hp => hp)
    (by
      intro a b
      cases a <;> cases b
      all_goals first | exact Or.inl rfl | exact Or.inr (fun h => B.noConfusion h))
  have hF : IsFirstUnmovedMover inPotency movesIn B.f :=
    ⟨⟨.x, .heat, trivial⟩, fun r hm => by cases r <;> exact hm⟩
  exact B.noConfusion (hB .f hF .m trivial)

namespace MutualPriority

/-! `m` moves `y` and is maximal in being, but `y`, less in being, is also simply
prior to `m`. -/

inductive B | m | y
inductive R | esse | heat

def more : B → B → Prop
  | .m, .m => False
  | .m, .y => True
  | .y, .m => False
  | .y, .y => False

def priorSimply : B → B → Prop
  | .m, .m => False
  | .m, .y => True
  | .y, .m => True
  | .y, .y => False

def inAct : B → R → Prop
  | .m, .esse => True
  | .m, .heat => True
  | .y, .esse => True
  | .y, .heat => False

def inPotency : B → R → Prop
  | .m, .esse => False
  | .m, .heat => False
  | .y, .esse => False
  | .y, .heat => True

def movesIn : B → B → R → Prop
  | .m, .m, .esse => False
  | .m, .m, .heat => False
  | .m, .y, .esse => False
  | .m, .y, .heat => True
  | .y, .m, .esse => False
  | .y, .m, .heat => False
  | .y, .y, .esse => False
  | .y, .y, .heat => False

def causesIn : B → B → R → Prop
  | .m, .m, .esse => True
  | .m, .m, .heat => True
  | .m, .y, .esse => True
  | .m, .y, .heat => True
  | .y, .m, .esse => False
  | .y, .m, .heat => False
  | .y, .y, .esse => False
  | .y, .y, .heat => False

end MutualPriority

/-- Without the *Metaphysics* II premise the bridge fails. In `MutualPriority`
every other premise of `firstMoverIsFirstBeing` holds (excluded middle as
decidable identity), and so do the *prima via* premises and act's simple
priority; the only first mover moved by none is the maximal being `m`, but `y` is
simply prior to it. Being maximal in being makes a being first only if what is
simply prior is more in being. -/
theorem withoutPriorMoreNotFirstBeing :
    ¬ ∀ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
      SomethingIsMovedReading MovedIn →
      MovedOnlyAsInPotencyReading MovedIn InPotency →
      MovesOnlyAsInActReading MovesIn InAct →
      ReducedOnlyByAMoverReading MovedIn MovesIn →
      NotActAndPotencyInSameRespectReading InAct InPotency →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply →
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      ActualityOnlyInsofarAsBeingReading InAct esse →
      CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverIsFirstBeing MovedIn MovesIn PriorSimply := by
  open MutualPriority in
  intro h
  have hB := h B R inPotency movesIn inPotency inAct (fun _ _ => False) priorSimply
    (fun _ => more) causesIn .esse .esse .esse .esse
    ⟨.y, .heat, trivial⟩
    (fun _ _ hm => hm)
    (by intro a b r hm; cases a <;> cases b <;> cases r <;> first | exact True.intro | exact False.elim hm)
    (by
      intro b r hm
      cases b <;> cases r
      all_goals first | exact False.elim hm | exact ⟨.m, trivial⟩)
    (by intro b r ⟨ha, hp⟩; cases b <;> cases r <;> first | exact False.elim ha | exact False.elim hp)
    (by
      intro a b r _ hmv ⟨r', hm⟩
      cases a <;> cases b <;> cases r <;> cases r'
      all_goals first | exact False.elim hmv | exact False.elim hm)
    (fun _ => Acc.intro _ fun _ h => False.elim h)
    (by
      intro b r hp
      cases b <;> cases r
      all_goals first | exact False.elim hp | exact ⟨.m, trivial, trivial⟩)
    ⟨⟨.m, .y, trivial⟩, ⟨.m, .y, trivial⟩, ⟨.m, .y, trivial⟩⟩
    (by
      intro r _
      refine ⟨.m, by cases r <;> exact True.intro, fun b hb => ?_⟩
      cases b <;> exact hb)
    (fun _ hm => hm)
    (by
      intro r b ⟨_, hNo⟩ a _ _
      cases b
      · cases a <;> cases r <;> exact True.intro
      · exact (hNo .m trivial).elim)
    (by intro b r _; cases b <;> exact True.intro)
    (by
      intro c a _ hne hc ⟨x, r, hm⟩
      cases a
      · cases c
        · exact (hne rfl).elim
        · exact False.elim hc
      · cases x <;> cases r <;> exact False.elim hm)
    (by
      intro a b
      cases a <;> cases b
      all_goals first | exact Or.inl rfl | exact Or.inr (fun h => B.noConfusion h))
  have hM : IsFirstUnmovedMover inPotency movesIn B.m :=
    ⟨⟨.y, .heat, trivial⟩, fun r hm => by cases r <;> exact hm⟩
  exact B.noConfusion (hB .m hM .y trivial)

namespace Joint

/-! `m` moves `y` in `other`; `y`, so moved, heats `x` (a per se link). `m` causes
the being of `y` and `x`, and `y` is a caused agent that is moved to act. -/

inductive B | m | y | x
inductive R | esse | heat | other

def more : B → B → Prop
  | .m, .m => False
  | .m, .y => True
  | .m, .x => True
  | .y, .m => False
  | .y, .y => False
  | .y, .x => True
  | .x, .m => False
  | .x, .y => False
  | .x, .x => False

def inAct : B → R → Prop
  | .m, .esse => True
  | .m, .heat => True
  | .m, .other => True
  | .y, .esse => True
  | .y, .heat => True
  | .y, .other => False
  | .x, .esse => True
  | .x, .heat => False
  | .x, .other => False

def inPotency : B → R → Prop
  | .m, .esse => False
  | .m, .heat => False
  | .m, .other => False
  | .y, .esse => False
  | .y, .heat => False
  | .y, .other => True
  | .x, .esse => False
  | .x, .heat => True
  | .x, .other => False

def movesIn : B → B → R → Prop
  | .m, .m, .esse => False
  | .m, .m, .heat => False
  | .m, .m, .other => False
  | .m, .y, .esse => False
  | .m, .y, .heat => False
  | .m, .y, .other => True
  | .m, .x, .esse => False
  | .m, .x, .heat => False
  | .m, .x, .other => False
  | .y, .m, .esse => False
  | .y, .m, .heat => False
  | .y, .m, .other => False
  | .y, .y, .esse => False
  | .y, .y, .heat => False
  | .y, .y, .other => False
  | .y, .x, .esse => False
  | .y, .x, .heat => True
  | .y, .x, .other => False
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .m, .other => False
  | .x, .y, .esse => False
  | .x, .y, .heat => False
  | .x, .y, .other => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False
  | .x, .x, .other => False

def movesAsMoved : B → B → Prop
  | .m, .m => False
  | .m, .y => False
  | .m, .x => False
  | .y, .m => False
  | .y, .y => False
  | .y, .x => True
  | .x, .m => False
  | .x, .y => False
  | .x, .x => False

def causesIn : B → B → R → Prop
  | .m, .m, .esse => True
  | .m, .m, .heat => True
  | .m, .m, .other => True
  | .m, .y, .esse => True
  | .m, .y, .heat => True
  | .m, .y, .other => True
  | .m, .x, .esse => True
  | .m, .x, .heat => True
  | .m, .x, .other => True
  | .y, .m, .esse => False
  | .y, .m, .heat => False
  | .y, .m, .other => False
  | .y, .y, .esse => False
  | .y, .y, .heat => False
  | .y, .y, .other => False
  | .y, .x, .esse => False
  | .y, .x, .heat => False
  | .y, .x, .other => False
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .m, .other => False
  | .x, .y, .esse => False
  | .x, .y, .heat => False
  | .x, .y, .other => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False
  | .x, .x, .other => False

theorem acc : ∀ b, Acc movesAsMoved b := by
  have hy : Acc movesAsMoved .y := Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hm : Acc movesAsMoved .m := Acc.intro _ fun a h => by cases a <;> exact False.elim h
  have hx : Acc movesAsMoved .x := Acc.intro _ fun a h => by
    cases a
    · exact False.elim h
    · exact hy
    · exact False.elim h
  intro b
  cases b
  · exact hm
  · exact hy
  · exact hx

end Joint

/-- The premises of the #147 results (`quartaVia`, `firstMoverIsMaximeEns`,
`firstMoverIsFirstBeing`, `oneFirstMoverViaMaximeEns` and
`firstMoverHasPerfectionsOfThings`), the seven *prima via* premises (#151) and act's
simple priority (#166) hold together in one finite model, with excluded middle
as decidable identity. The model also witnesses a per se link and a caused agent
that moves and is moved, so the q.105 a.5 premise does not hold only vacuously. -/
theorem premisesJointlySatisfiable :
    ∃ (Being Respect : Type)
      (MovedIn : Being → Respect → Prop)
      (MovesIn : Being → Being → Respect → Prop)
      (InPotency InAct : Being → Respect → Prop)
      (MovesAsMoved PriorSimply : Being → Being → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
      SomethingIsMovedReading MovedIn ∧
      MovedOnlyAsInPotencyReading MovedIn InPotency ∧
      MovesOnlyAsInActReading MovesIn InAct ∧
      ReducedOnlyByAMoverReading MovedIn MovesIn ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved ∧
      NoInfinitePerSeMoverSeriesReading MovesAsMoved ∧
      ActSimplyPriorToPotencyReading InAct InPotency PriorSimply ∧
      GradesFoundInThingsReading MoreIn bonum verum nobile ∧
      GradesByApproachToAMaximumReading InAct MoreIn ∧
      MostTrueIsMostBeingReading InAct MoreIn verum esse ∧
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      ActualityOnlyInsofarAsBeingReading InAct esse ∧
      CausedAgentIsMovedToActReading MovedIn MovesIn InAct CausesIn esse ∧
      PriorAsCauseIsMoreInBeingReading PriorSimply MoreIn esse ∧
      PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse ∧
      (∀ a b : Being, a = b ∨ a ≠ b) ∧
      (∃ y x, MovesAsMoved y x) ∧
      (∃ c a x r r', a ≠ c ∧ CausesIn c a esse ∧ MovesIn a x r ∧ MovedIn a r') := by
  open Joint in
  refine ⟨B, R, inPotency, movesIn, inPotency, inAct, movesAsMoved, more,
    (fun _ => more), causesIn, .esse, .esse, .esse, .esse, ⟨.x, .heat, trivial⟩,
    fun _ _ hm => hm, ?_, ?_, ?_, ?_, acc, ?_, ⟨⟨.m, .y, trivial⟩, ⟨.m, .y, trivial⟩,
    ⟨.m, .y, trivial⟩⟩, ?_, fun _ hm => hm, ?_, ?_, ?_, fun _ _ hp => hp, ?_, ?_,
    ⟨.y, .x, trivial⟩,
    ⟨.m, .y, .x, .heat, .other, fun h => B.noConfusion h, trivial, trivial, trivial⟩⟩
  · intro a b r hm
    cases a <;> cases b <;> cases r <;> first | exact True.intro | exact False.elim hm
  · intro b r hm
    cases b <;> cases r
    all_goals first | exact False.elim hm | exact ⟨.m, trivial⟩ | exact ⟨.y, trivial⟩
  · intro b r ⟨ha, hp⟩
    cases b <;> cases r <;> first | exact False.elim ha | exact False.elim hp
  · intro a b r _ hmv ⟨r', hm⟩
    cases a <;> cases b <;> cases r <;> cases r'
    all_goals first | exact True.intro | exact False.elim hmv | exact False.elim hm
  · intro b r hp
    cases b <;> cases r
    all_goals first
      | exact False.elim hp
      | exact ⟨.m, trivial, trivial⟩
      | exact ⟨.y, trivial, trivial⟩
  · intro r _
    refine ⟨.m, by cases r <;> exact True.intro, fun b hb => ?_⟩
    cases b <;> exact hb
  · intro r b ⟨_, hNo⟩ a _ _
    cases b
    · cases a <;> cases r <;> exact True.intro
    · exact (hNo .m trivial).elim
    · exact (hNo .m trivial).elim
  · intro b r hb
    cases b <;> cases r <;> first | exact True.intro | exact False.elim hb
  · intro c a hc hne _ ⟨t, r, hm⟩
    cases a
    · -- only `m` causes the being of all others, and then `a ≠ c` fails
      cases c
      · exact (hne rfl).elim
      · exact (hc .m (fun h => B.noConfusion h) trivial).elim
      · exact (hc .m (fun h => B.noConfusion h) trivial).elim
    · exact ⟨.other, trivial⟩
    · cases t <;> cases r <;> exact False.elim hm
  · intro c b r hc _
    cases c <;> cases b <;> cases r <;> first | exact True.intro | exact False.elim hc
  · intro a b
    cases a <;> cases b
    all_goals first | exact Or.inl rfl | exact Or.inr (fun h => B.noConfusion h)
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsFirstBeing
