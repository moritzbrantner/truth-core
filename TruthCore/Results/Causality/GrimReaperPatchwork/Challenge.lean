import TruthCore.Causality.GrimReaperPatchwork
import TruthCore.Results.Causality.ComingToBeHorns.Solution
import TruthCore.Results.Causality.BegunComingToBe.Solution
import TruthCore.Results.Causality.IndexedSignalReaper.Solution

namespace TruthCore.Results.Causality.GrimReaperPatchwork
open TruthCore.Causality.GrimReaperPatchwork
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.ComingToBeHorns (PopulatedPastsFounded
  PossiblyEarlierGroundedPopulated GroundsPrecedeAt)
open TruthCore.Causality.ContingentComingToBe (AllContingentsComeToBeAt)
open TruthCore.Causality.IndexedSignalProvenance (IndexAdmissible)
open TruthCore.Causality.IndexedSignalReaper (PositiveTrigger Emission Forwarding)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)

/-- The index of a moment on an injective descent, if it lies on it. -/
noncomputable def indexOn {T : Type} (c : Nat → T) (r : T) : Option Nat := by
  classical
  exact if hr : ∃ j, c j = r then some (Nat.find hr) else none

/-- Read a glued world's registers along a descent as a `Nat`-indexed signal:
station `n`'s output code, translated to the index of the station it names. -/
noncomputable def signalOf {W T : Type} (R : ReaperFrame W T) (u : W)
    (c : Nat → T) (n : Nat) : Option Nat :=
  (R.out u (c n)).bind (indexOn c)

/-- Horn H2 (non-well-founded populated past) priced by Reaper patchwork. If,
along every descent below a populated moment of an accessible history, adjacent
Reaper pieces are co-possible, and co-possible adjacent pieces glue into one
possible arrangement, every populated moment has a founded past: otherwise the
glued arrangement along a descent below it would exist, and no world realizes
one. -/
theorem populatedPastsFoundedOfPatchwork {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPieces : ReaperPiecesPossible R h Concrete w)
    (hPatch : ReaperPatchwork R h Concrete w) :
    PopulatedPastsFounded h Concrete w := by
  sorry

/-- The begun version of horn H2 priced by coinitial Reaper patchwork. If,
along every coinitial descent below a populated moment, adjacent Reaper pieces
are co-possible and glue, and every beginningless populated past has a
coinitial descent, every populated moment has a past with a beginning. -/
theorem populatedPastsBegunOfPatchwork {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPieces : CoinitialReaperPiecesPossible R h Concrete w)
    (hPatch : CoinitialReaperPatchwork R h Concrete w)
    (hCount : BeginninglessPastsCountablyCoinitial h Concrete w) :
    PopulatedPastsBegun h Concrete w := by
  sorry

/-- Premise A3′w of the modal spine (possible begun coming-to-be) from begun
populated pasts and the possibility of a populated history whose contingent
concrete things all have earlier-present concrete grounds. -/
theorem possiblyBegunOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hPast : PopulatedPastsBegun h Concrete w)
    (hPossible : PossiblyEarlierGroundedPopulated h Concrete grounds w) :
    PossiblyBegunComingToBe h Concrete w := by
  sorry

/-- Strength order: founded populated pasts give begun populated pasts. -/
theorem populatedPastsBegunOfFounded {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hFounded : PopulatedPastsFounded h Concrete w) :
    PopulatedPastsBegun h Concrete w := by
  sorry

/-- Strength order: local pieces along every descent give local pieces along
every coinitial descent. -/
theorem coinitialPiecesOfPieces {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPieces : ReaperPiecesPossible R h Concrete w) :
    CoinitialReaperPiecesPossible R h Concrete w := by
  sorry

/-- Strength order: patchwork along every descent gives patchwork along every
coinitial descent. -/
theorem coinitialPatchworkOfPatchwork {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPatch : ReaperPatchwork R h Concrete w) :
    CoinitialReaperPatchwork R h Concrete w := by
  sorry

open TruthCore.Causality.GrimReaperPatchwork.Control
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

/-- Independence and nonvacuity controls. -/
theorem controls : TruthCore.Causality.GrimReaperPatchwork.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.GrimReaperPatchwork
