import TruthCore.Causality.MetricGrimReaper
import TruthCore.Results.Causality.GrimReaperPatchwork.Solution

namespace TruthCore.Results.Causality.MetricGrimReaper
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.GrimReaperPatchwork
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.ComingToBeHorns (PopulatedPastsFounded
  PossiblyEarlierGroundedPopulated)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Horn H2 priced metrically. If, along every spaced descent below a populated
moment of an accessible history, adjacent Reaper pieces are co-possible and
co-possible adjacent pieces glue into one possible arrangement, then in linear
time every populated moment has a metrically finite past: otherwise a spaced
descent below it carries a glued arrangement, and no world realizes one. -/
theorem populatedPastsMetricallyFiniteOfPatchwork {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (w : W) (hPieces : SpacedReaperPiecesPossible R h Concrete k w)
    (hPatch : SpacedReaperPatchwork R h Concrete k w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  sorry

/-- Strength order: coinitial local pieces give spaced local pieces. -/
theorem spacedPiecesOfCoinitial {W B T : Type} [LinearOrder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hPieces : CoinitialReaperPiecesPossible R h Concrete w) :
    SpacedReaperPiecesPossible R h Concrete k w := by
  sorry

/-- Strength order: coinitial patchwork gives spaced patchwork. -/
theorem spacedPatchworkOfCoinitial {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (w : W) (hPatch : CoinitialReaperPatchwork R h Concrete w) :
    SpacedReaperPatchwork R h Concrete k w := by
  sorry

/-- Strength order: begun populated pasts give metrically finite populated
pasts (linear time, any real clock). -/
theorem populatedPastsMetricallyFiniteOfBegun {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hBegun : PopulatedPastsBegun h Concrete w) :
    PopulatedPastsMetricallyFinite h Concrete k w := by
  sorry

open TruthCore.Causality.MetricGrimReaper.Control
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot quietFrame pivotFrame)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.BegunComingToBe.Control (predecessorGrounds)
open TruthCore.Results.Causality.GrimReaperPatchwork
  (pivotOne pivotPopulated pivotDescent pivotCoinitial pivotPiecesPossible
    quietNoPiece)

/-- Halving from a positive real moment. -/
noncomputable def halving (t : PosReal) (n : Nat) : PosReal :=
  ⟨t.1 / 2 ^ n, div_pos t.2 (pow_pos two_pos n)⟩

/-- Independence, nonvacuity and reach controls. -/
theorem controls : TruthCore.Causality.MetricGrimReaper.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.MetricGrimReaper
