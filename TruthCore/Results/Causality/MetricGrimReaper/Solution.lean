module

public import TruthCore.Causality.MetricGrimReaper
public import TruthCore.Results.Causality.GrimReaperPatchwork.Solution

@[expose] public section

namespace TruthCore.Results.Causality.MetricGrimReaper
open TruthCore.Causality.MetricGrimReaper
open TruthCore.Causality.GrimReaperPatchwork
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.ComingToBeHorns (PopulatedPastsFounded
  PossiblyEarlierGroundedPopulated)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)

/-- Along a spaced descent the readings fall by at least `δ` per slot. -/
theorem readingLe {T : Type} [Preorder T] (k : TimeClock T) (c : Nat → T) (δ : ℝ)
    (hδ : ∀ n, δ ≤ k.reading (c n) - k.reading (c (n + 1))) (n : Nat) :
    k.reading (c n) ≤ k.reading (c 0) - n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := hδ n
    push_cast
    linarith

/-- Along a descent every member lies at or before the first. -/
theorem descentLe {T : Type} [Preorder T] (c : Nat → T) (hDesc : Descent c) (n : Nat) :
    c n ≤ c 0 := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (le_of_lt (hDesc n)) ih

/-- Along a spaced descent the readings fall below every real number. -/
theorem readingsUnbounded {T : Type} [Preorder T] (k : TimeClock T) (c : Nat → T)
    (hSlots : SlotsAtLeast k c) (L : ℝ) : ∃ n, k.reading (c n) < L := by
  obtain ⟨δ, hδ, hSlot⟩ := hSlots
  obtain ⟨n, hn⟩ := exists_nat_gt ((k.reading (c 0) - L) / δ)
  refine ⟨n, lt_of_le_of_lt (readingLe k c δ hSlot n) ?_⟩
  rw [div_lt_iff₀ hδ] at hn
  linarith

/-- A spaced descent starts at a moment whose past is metrically infinite. -/
theorem unboundedOfSpaced {T : Type} [Preorder T] (k : TimeClock T) (c : Nat → T)
    (hDesc : Descent c) (hSlots : SlotsAtLeast k c) :
    ¬ MetricallyFinitePast k (c 0) := by
  rintro ⟨L, hL⟩
  obtain ⟨n, hn⟩ := readingsUnbounded k c hSlots L
  exact absurd (hL ⟨c n, descentLe c hDesc n, rfl⟩) (not_le.mpr hn)

/-- In linear time, a moment whose past is metrically infinite starts a
descent with slots of length at least one. -/
theorem spacedDescentOfUnbounded {T : Type} [LinearOrder T] (k : TimeClock T) (t : T)
    (hInf : ¬ MetricallyFinitePast k t) :
    ∃ c : Nat → T, c 0 = t ∧ Descent c ∧ SlotsAtLeast k c := by
  unfold MetricallyFinitePast at hInf
  rw [not_bddBelow_iff] at hInf
  have hBelow : ∀ L : ℝ, ∃ s, s ≤ t ∧ k.reading s < L := by
    intro L
    obtain ⟨_, ⟨s, hs, rfl⟩, hlt⟩ := hInf L
    exact ⟨s, hs, hlt⟩
  choose pick _ hLt using hBelow
  let c : Nat → T := fun n => Nat.rec t (fun _ x => pick (k.reading x - 1)) n
  have hRead : ∀ n, k.reading (c (n + 1)) < k.reading (c n) - 1 := fun n => hLt _
  refine ⟨c, rfl, ?_, 1, one_pos, ?_⟩
  · intro n
    exact k.strictMono.lt_iff_lt.mp (by linarith [hRead n])
  · intro n
    linarith [hRead n]

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
  intro v hwv x t hx hCont hxt
  by_contra hInf
  obtain ⟨c, hc0, hDesc, hSlots⟩ := spacedDescentOfUnbounded k t hInf
  have hPop : PopulatedAt h Concrete v (c 0) := ⟨x, hx, hCont, hc0 ▸ hxt⟩
  obtain ⟨u, _, hAll⟩ :=
    hPatch v hwv c hDesc hSlots hPop (hPieces v hwv c hDesc hSlots hPop)
  exact TruthCore.Results.Causality.GrimReaperPatchwork.arrangementImpossible
    R u c hDesc hAll

/-- In linear time a spaced descent is coinitial: it runs below every earlier
moment. -/
theorem coinitialOfSpaced {T : Type} [LinearOrder T] (k : TimeClock T) (c : Nat → T)
    (hSlots : SlotsAtLeast k c) : Coinitial c := by
  intro s _
  obtain ⟨n, hn⟩ := readingsUnbounded k c hSlots (k.reading s)
  exact ⟨n, k.strictMono.lt_iff_lt.mp hn⟩

/-- Strength order: coinitial local pieces give spaced local pieces. -/
theorem spacedPiecesOfCoinitial {W B T : Type} [LinearOrder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hPieces : CoinitialReaperPiecesPossible R h Concrete w) :
    SpacedReaperPiecesPossible R h Concrete k w :=
  fun v hwv c hDesc hSlots hPop =>
    hPieces v hwv c hDesc (coinitialOfSpaced k c hSlots) hPop

/-- Strength order: coinitial patchwork gives spaced patchwork. -/
theorem spacedPatchworkOfCoinitial {W B T : Type} [LinearOrder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (k : TimeClock T)
    (w : W) (hPatch : CoinitialReaperPatchwork R h Concrete w) :
    SpacedReaperPatchwork R h Concrete k w :=
  fun v hwv c hDesc hSlots hPop =>
    hPatch v hwv c hDesc (coinitialOfSpaced k c hSlots) hPop

/-- In linear time a past with a beginning is metrically finite: the first
moment's reading bounds it below. -/
theorem metricallyFiniteOfBegun {T : Type} [LinearOrder T] (k : TimeClock T) (t : T)
    (hBegun : BegunAt t) : MetricallyFinitePast k t := by
  obtain ⟨m, _, hMin⟩ := hBegun
  refine ⟨k.reading m, ?_⟩
  rintro _ ⟨s, _, rfl⟩
  exact k.strictMono.monotone (not_lt.mp (hMin s))

/-- Strength order: begun populated pasts give metrically finite populated
pasts (linear time, any real clock). -/
theorem populatedPastsMetricallyFiniteOfBegun {W B T : Type} [LinearOrder T]
    (h : History W B T) (Concrete : B → Prop) (k : TimeClock T) (w : W)
    (hBegun : PopulatedPastsBegun h Concrete w) :
    PopulatedPastsMetricallyFinite h Concrete k w :=
  fun v hwv x t hx hCont hxt =>
    metricallyFiniteOfBegun k t (hBegun v hwv x t hx hCont hxt)

open TruthCore.Causality.MetricGrimReaper.Control
open TruthCore.Causality.GrimReaperPatchwork.Control (pivot quietFrame pivotFrame)
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.BegunComingToBe.Control (predecessorGrounds)
open TruthCore.Results.Causality.GrimReaperPatchwork
  (pivotOne pivotPopulated pivotDescent pivotCoinitial pivotPiecesPossible
    quietNoPiece)

/-- Every past of positive real time is metrically finite. -/
theorem posFinite (t : PosReal) : MetricallyFinitePast posClock t := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, _, rfl⟩
  exact le_of_lt s.2

/-- Every past of non-negative real time is metrically finite. -/
theorem nnFinite (t : NNReal) : MetricallyFinitePast nnClock t := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, _, rfl⟩
  exact s.2

/-- No positive real moment has a past with a beginning. -/
theorem posNotBegun (t : PosReal) : ¬ BegunAt t := by
  rintro ⟨m, _, hMin⟩
  refine hMin ⟨m.1 / 2, by linarith [m.2]⟩ ?_
  show m.1 / 2 < m.1
  linarith [m.2]

/-- Halving from a positive real moment. -/
noncomputable def halving (t : PosReal) (n : Nat) : PosReal :=
  ⟨t.1 / 2 ^ n, div_pos t.2 (pow_pos two_pos n)⟩

theorem halvingDescent (t : PosReal) : Descent (halving t) := by
  intro n
  show t.1 / 2 ^ (n + 1) < t.1 / 2 ^ n
  rw [pow_succ]
  have := t.2
  have hp : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  rw [div_lt_div_iff₀ (by positivity) hp]
  nlinarith

theorem halvingCoinitial (t : PosReal) : Coinitial (halving t) := by
  intro s _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos s.2 t.2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  show t.1 / 2 ^ n < s.1
  have ht := t.2
  rw [div_pow, one_pow, lt_div_iff₀ ht, div_mul_eq_mul_div, one_mul] at hn
  exact hn

theorem openBelowContingent (x : Int) : ContingentAt openBelow.ontic true x :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

theorem openBelowCoinitial : BeginninglessPastsCountablyCoinitial openBelow all true :=
  fun _ _ t _ _ => ⟨halving t, by simp [halving], halvingDescent t, halvingCoinitial t⟩

theorem openBelowNotBegun : ¬ PopulatedPastsBegun openBelow all true := fun hB =>
  posNotBegun ⟨1, one_pos⟩
    (hB true trivial 0 ⟨1, one_pos⟩ trivial (openBelowContingent 0) rfl)

/-- In non-negative real time no moment after `0` has a founded past. -/
theorem nnNotAcc (t : NNReal) (ht : 0 < t) : ¬ Acc (fun a b : NNReal => a < b) t := by
  intro hAcc
  induction hAcc with
  | intro t _ ih =>
    have ht' : (0 : ℝ) < t := ht
    exact ih (t / 2) (by
      show ((t / 2 : NNReal) : ℝ) < t
      push_cast; linarith) (by
      show (0 : ℝ) < ((t / 2 : NNReal) : ℝ)
      push_cast; linarith)

theorem firstMomentContingent : ContingentAt firstMoment.ontic true () :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

theorem firstMomentNotFounded : ¬ PopulatedPastsFounded firstMoment all true := fun hF =>
  nnNotAcc 1 one_pos (hF true trivial () 1 trivial firstMomentContingent ⟨rfl, one_pos⟩)

theorem firstMomentBegun : PopulatedPastsBegun firstMoment all true := by
  intro v _ x t _ _ hxt
  exact ⟨0, Or.inr hxt.2, fun _ => not_lt_zero⟩

theorem pivotNotFinite : ¬ PopulatedPastsMetricallyFinite pivot all intClock 1 := by
  intro hF
  have hFin := hF 1 trivial 0 0 trivial ⟨pivotOne, 0, trivial, fun h => h rfl⟩
    ⟨pivotOne, le_refl _⟩
  have hSlots : SlotsAtLeast intClock (fun n : Nat => -(n : Int)) := by
    refine ⟨1, one_pos, fun n => ?_⟩
    show (1 : ℝ) ≤ ((-(n : Int) : Int) : ℝ) - ((-((n + 1 : Nat) : Int) : Int) : ℝ)
    push_cast; linarith
  exact unboundedOfSpaced intClock _ pivotDescent hSlots (by simpa using hFin)

/-- Independence, nonvacuity and reach controls. -/
theorem controls : TruthCore.Causality.MetricGrimReaper.Control.Certificate := by
  have hQuietPatch : SpacedReaperPatchwork (quietFrame Int Int) pivot all intClock 1 := by
    intro _ _ c _ _ _ hAdj
    obtain ⟨_, _, hp, _⟩ := hAdj 0
    exact (quietNoPiece _ c 0 hp).elim
  have hPivotPieces : SpacedReaperPiecesPossible pivotFrame pivot all intClock 1 :=
    spacedPiecesOfCoinitial _ _ _ _ _
      (TruthCore.Results.Causality.GrimReaperPatchwork.coinitialPiecesOfPieces _ _ _ _
        pivotPiecesPossible)
  refine ⟨⟨hQuietPatch, ?_, hPivotPieces, ?_, pivotNotFinite⟩,
    ⟨?_, ?_, fun _ _ _ t _ _ _ => posFinite t, openBelowNotBegun, openBelowCoinitial,
      ?_, ?_⟩,
    ⟨?_, fun _ _ _ t _ _ _ => nnFinite t, firstMomentBegun, firstMomentNotFounded, ?_⟩⟩
  · intro hPieces
    exact pivotNotFinite (populatedPastsMetricallyFiniteOfPatchwork _ _ _ _ _
      hPieces hQuietPatch)
  · intro hPatch
    exact pivotNotFinite (populatedPastsMetricallyFiniteOfPatchwork _ _ _ _ _
      hPivotPieces hPatch)
  · intro R
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ c hDesc hSlots _
      exact (unboundedOfSpaced posClock c hDesc hSlots (posFinite _)).elim
    · intro _ _ c hDesc hSlots _
      exact (unboundedOfSpaced posClock c hDesc hSlots (posFinite _)).elim
    · rintro ⟨hPieces, hPatch⟩
      exact openBelowNotBegun
        (TruthCore.Results.Causality.GrimReaperPatchwork.populatedPastsBegunOfPatchwork
          R openBelow all true hPieces hPatch openBelowCoinitial)
  · intro hPieces
    have hPop : PopulatedAt openBelow all true (halving ⟨1, one_pos⟩ 0) :=
      ⟨0, trivial, openBelowContingent 0, rfl⟩
    obtain ⟨_, _, hp, _⟩ := hPieces true trivial _ (halvingDescent _)
      (halvingCoinitial _) hPop 0
    exact quietNoPiece _ _ 0 hp
  · refine ⟨true, trivial, ⟨0, ⟨1, one_pos⟩, trivial, openBelowContingent 0, rfl⟩, ?_, ?_⟩
    · intro x _ _ _
      exact ⟨x - 1, trivial, rfl, rfl, rfl⟩
    · intro x y t _ _ hyx _
      obtain ⟨_, rfl⟩ := hyx
      refine ⟨⟨t.1 / 2, by linarith [t.2]⟩, ?_, rfl⟩
      show t.1 / 2 < t.1
      linarith [t.2]
  · rintro ⟨v, _, _, x, t, _, _, _, hBegun⟩
    exact posNotBegun t hBegun
  · intro R
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ c hDesc hSlots _
      exact (unboundedOfSpaced nnClock c hDesc hSlots (nnFinite _)).elim
    · intro _ _ c hDesc hSlots _
      exact (unboundedOfSpaced nnClock c hDesc hSlots (nnFinite _)).elim
    · rintro ⟨hPieces, hPatch⟩
      exact firstMomentNotFounded
        (TruthCore.Results.Causality.GrimReaperPatchwork.populatedPastsFoundedOfPatchwork
          R firstMoment all true hPieces hPatch)
  · refine ⟨true, trivial, ?_, (), 1, trivial, firstMomentContingent, ⟨rfl, one_pos⟩, ?_⟩
    · intro x _ _ t hxt
      exact ⟨0, hxt.2, fun h => lt_irrefl _ h.2⟩
    · exact ⟨0, Or.inr one_pos, fun _ => not_lt_zero⟩

end TruthCore.Results.Causality.MetricGrimReaper
