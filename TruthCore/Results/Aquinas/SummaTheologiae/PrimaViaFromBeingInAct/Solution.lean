import TruthCore.Results.Aquinas.SummaTheologiae.PrimaVia.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The *prima via* from the literal reading of *nisi per aliquod ens in actu*
(`ReducedOnlyByABeingInActReading`) in place of the two premises "whatever is
moved has a mover" and "every mover is in act in the respect in which it moves".

The proof composes the existing `PrimaVia.primaVia`. It restricts moving to
moving by a mover in act: `y` moves-in-act `x` in `r` when `y` moves `x` in `r`
and is in act in `r`. For that relation every mover is in act by construction,
the being-in-act reading says that whatever is moved has such a mover, and a
per se link of the restricted relation is a per se link of the original one.
`primaVia` then yields that a first mover moved by none cannot be lacking for
the restricted relation, hence for moving itself.

So the *prima via* does not need that *every* mover is in act, only that each
moved thing has *some* mover in act; `BeingInActReadingFacts` shows that this is
strictly weaker. -/
theorem primaViaFromBeingInAct {Being : Type} {Respect : Type}
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (InPotency InAct : Being → Respect → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hSense : SomethingIsMovedReading MovedIn)
    (hPotency : MovedOnlyAsInPotencyReading MovedIn InPotency)
    (hReduction : ReducedOnlyByABeingInActReading MovedIn MovesIn InAct)
    (hNotBoth : NotActAndPotencyInSameRespectReading InAct InPotency)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    FirstUnmovedMoverCannotBeLackingReading MovedIn MovesIn := by
  -- moving restricted to movers in act in the respect
  let MovesInAct : Being → Being → Respect → Prop := fun y x r => MovesIn y x r ∧ InAct y r
  -- INF-AQUINAS-ST-I-Q2-A3-PRIMA-VIA-FROM-BEING-IN-ACT (result AQUINAS-ST-I-Q2-A3-PRIMA-VIA)
  have hRestricted : FirstUnmovedMoverCannotBeLackingReading MovedIn MovesInAct :=
    PrimaVia.primaVia MovedIn MovesInAct InPotency InAct MovesAsMoved hSense hPotency
      (fun _ _ _ hMoves => hMoves.2)
      hReduction
      hNotBoth
      (fun y x r hDistinct hMoves hMoved => hPerSe y x r hDistinct hMoves.1 hMoved)
      hRegress
  -- a first mover of the restricted relation is a first mover
  intro hNoFirst
  exact hRestricted fun ⟨f, ⟨x, r, hMoves⟩, hUnmoved⟩ =>
    hNoFirst ⟨f, ⟨x, r, hMoves.1⟩, hUnmoved⟩

/-- Each premise of `primaViaFromBeingInAct` is needed (omission countermodels
in `ActPotencyModels`). -/
theorem premisesNeeded : PrimaViaFromBeingInActPremisesNeeded :=
  ActPotencyModels.primaViaFromBeingInActPremisesNeeded

end TruthCore.Results.Aquinas.SummaTheologiae.PrimaViaFromBeingInAct
