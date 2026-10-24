import TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEns.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2
namespace TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverHasPerfectionsOfThings
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism (FirstUnmovedMoverHasEveryPerfectionOfThings
  FirstUnmovedMoverHasEveryPerfection IsFirstUnmovedMover)

/-- ST I q.4 a.2 co., first proof, for the *prima via*'s mover. Every first mover
moved by none is the maximal being `m` of the *quarta via*. Whatever perfection
any other being has, it has being (q.4 a.1 ad 3), so `m` causes its being, and
the perfections of an effect pre-exist in its effective cause; so `m` has that
perfection too, formally or eminently. -/
theorem firstMoverHasPerfectionsOfThings {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InAct : Being → Respect → Prop)
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
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse)
    (hEM : TruthCore.Logic.ExcludedMiddle) :
    FirstUnmovedMoverHasEveryPerfectionOfThings MovedIn MovesIn InAct := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUARTA-VIA (result AQUINAS-ST-I-Q2-A3-QUARTA-VIA)
  obtain ⟨m, hMax, hCauses⟩ := QuartaVia.quartaVia InAct MoreIn CausesIn bonum verum
    nobile esse hGrades hApproach hTrue hGenus
  -- INF-AQUINAS-FIRST-MOVER-IS-MAXIME-ENS (result AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-MAXIME-ENS)
  have hIdent := FirstMoverIsMaximeEns.firstMoverIsMaximeEns MovedIn MovesIn InAct
    MoreIn CausesIn esse hGenus hInAct hBeing hApplied hEM
  -- INF-AQUINAS-ST-I-Q4-A2-FIRST-MOVER-HAS-PERFECTIONS-OF-THINGS: m has every
  -- perfection found in things
  have hMaxPerfect : ∀ x r, InAct x r → InAct m r := by
    intro x r hx
    cases hEM (x = m) with
    | inl hSame => rw [← hSame]; exact hx
    | inr hOther => exact hPreexist m x r (hCauses x hOther (hBeing x r hx)) hx
  -- and every first mover moved by none is m
  intro f hF x r hx
  rw [hIdent f hF m hMax]
  exact hMaxPerfect x r hx

namespace Unhad

/-! `m` heats `x`; nothing is in act as to `cold`. -/

inductive B | m | x
inductive R | esse | heat | cold

def moreIn : R → B → B → Prop
  | .esse, .m, .m => False
  | .esse, .m, .x => True
  | .esse, .x, .m => False
  | .esse, .x, .x => False
  | .heat, .m, .m => False
  | .heat, .m, .x => True
  | .heat, .x, .m => False
  | .heat, .x, .x => False
  | .cold, .m, .m => False
  | .cold, .m, .x => False
  | .cold, .x, .m => False
  | .cold, .x, .x => False

def inAct : B → R → Prop
  | .m, .esse => True
  | .m, .heat => True
  | .m, .cold => False
  | .x, .esse => True
  | .x, .heat => False
  | .x, .cold => False

def inPotency : B → R → Prop
  | .m, .esse => False
  | .m, .heat => False
  | .m, .cold => False
  | .x, .esse => False
  | .x, .heat => True
  | .x, .cold => False

def movesIn : B → B → R → Prop
  | .m, .m, .esse => False
  | .m, .m, .heat => False
  | .m, .m, .cold => False
  | .m, .x, .esse => False
  | .m, .x, .heat => True
  | .m, .x, .cold => False
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .m, .cold => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False
  | .x, .x, .cold => False

def priorSimply : B → B → Prop
  | .m, .m => False
  | .m, .x => True
  | .x, .m => False
  | .x, .x => False

def causesIn : B → B → R → Prop
  | .m, .m, .esse => True
  | .m, .m, .heat => True
  | .m, .m, .cold => True
  | .m, .x, .esse => True
  | .m, .x, .heat => True
  | .m, .x, .cold => True
  | .x, .m, .esse => False
  | .x, .m, .heat => False
  | .x, .m, .cold => False
  | .x, .x, .esse => False
  | .x, .x, .heat => False
  | .x, .x, .cold => False

end Unhad

/-- The strong bridge `FirstUnmovedMoverHasEveryPerfection` (act in *every*
respect) does not follow. In `Unhad` every premise of
`firstMoverHasPerfectionsOfThings` holds (excluded middle as decidable identity),
and so do the seven *prima via* premises and act's simple priority; but no being
is in act as to `cold`, so the first mover moved by none `m` is not either. The
first proof of q.4 a.2 reaches only the perfections found in things. -/
theorem everyRespectNotDerived :
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
      PerfectionsOfEffectPreexistInCauseReading InAct CausesIn esse →
      (∀ a b : Being, a = b ∨ a ≠ b) →
      FirstUnmovedMoverHasEveryPerfection MovedIn MovesIn InAct := by
  open Unhad in
  intro h
  have hB := h B R inPotency movesIn inPotency inAct (fun _ _ => False) priorSimply
    moreIn causesIn .esse .esse .esse .esse
    ⟨.x, .heat, trivial⟩
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
    ⟨⟨.m, .x, trivial⟩, ⟨.m, .x, trivial⟩, ⟨.m, .x, trivial⟩⟩
    (by
      intro r ⟨a, b, hab⟩
      cases r
      · exact ⟨.m, trivial, fun c hc => by cases c <;> exact hc⟩
      · exact ⟨.m, trivial, fun c hc => by cases c <;> exact hc⟩
      · cases a <;> cases b <;> exact False.elim hab)
    (fun _ hm => hm)
    (by
      intro r b ⟨hb, hNo⟩ a _ _
      cases b
      · cases a <;> cases r <;> exact True.intro
      · cases r
        · exact (hNo .m trivial).elim
        · exact False.elim hb
        · exact False.elim hb)
    (by intro b r hb; cases b <;> cases r <;> first | exact True.intro | exact False.elim hb)
    (by
      intro c a _ hne hc ⟨t, r, hm⟩
      cases a
      · cases c
        · exact (hne rfl).elim
        · exact False.elim hc
      · cases t <;> cases r <;> exact False.elim hm)
    (by
      intro c a r hc ha
      cases c
      · cases a <;> cases r <;> first | exact True.intro | exact False.elim ha
      · cases a <;> exact False.elim hc)
    (by
      intro a b
      cases a <;> cases b
      all_goals first | exact Or.inl rfl | exact Or.inr (fun h => B.noConfusion h))
  have hM : IsFirstUnmovedMover inPotency movesIn B.m :=
    ⟨⟨.x, .heat, trivial⟩, fun r hm => by cases r <;> exact hm⟩
  exact hB .m hM .cold
end TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverHasPerfectionsOfThings
