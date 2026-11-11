module

public import TruthCore.Causality.GrimReaperPatchwork
public import TruthCore.Results.Causality.ComingToBeHorns.Solution
public import TruthCore.Results.Causality.BegunComingToBe.Solution
public import TruthCore.Results.Causality.IndexedSignalReaper.Solution

@[expose] public section

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

theorem indexOn_eq {T : Type} (c : Nat → T) (hInj : Function.Injective c)
    (j : Nat) : indexOn c (c j) = some j := by
  classical
  unfold indexOn
  split_ifs with hr
  · exact congrArg some (hInj (Nat.find_spec hr))
  · exact absurd ⟨j, rfl⟩ hr

/-- Read a glued world's registers along a descent as a `Nat`-indexed signal:
station `n`'s output code, translated to the index of the station it names. -/
noncomputable def signalOf {W T : Type} (R : ReaperFrame W T) (u : W)
    (c : Nat → T) (n : Nat) : Option Nat :=
  (R.out u (c n)).bind (indexOn c)

theorem signalOf_some {W T : Type} (R : ReaperFrame W T) (u : W) (c : Nat → T)
    (n : Nat) (r : T) (hr : R.out u (c n) = some r) :
    signalOf R u c n = indexOn c r := by
  simp [signalOf, hr]

theorem signalOf_none {W T : Type} (R : ReaperFrame W T) (u : W) (c : Nat → T)
    (n : Nat) (hr : R.out u (c n) = none) : signalOf R u c n = none := by
  simp [signalOf, hr]

/-- No world realizes every Reaper piece along a strictly descending sequence of
moments: its registers, read as a `Nat`-indexed signal, would satisfy the four
local rules that `IndexedSignalReaper.impossible` refutes. -/
theorem arrangementImpossible {W T : Type} [Preorder T] (R : ReaperFrame W T)
    (u : W) (c : Nat → T) (hDesc : Descent c) : ¬ ∀ n, PieceAt R u c n := by
  intro hAll
  have hInj := TruthCore.Results.Causality.ComingToBeHorns.descentInjective c hDesc
  -- every present code names a station at or upstream of its own
  have hNamed : ∀ n r, R.out u (c n) = some r →
      ∃ j, n ≤ j ∧ r = c j ∧ signalOf R u c n = some j := by
    intro n r hr
    obtain ⟨j, hnj, rfl⟩ := (hAll n).2.2.2 r hr
    exact ⟨j, hnj, rfl, (signalOf_some R u c n _ hr).trans (indexOn_eq c hInj j)⟩
  apply TruthCore.Results.Causality.IndexedSignalReaper.impossible
    (signalOf R u c) (fun n => R.issues u (c n))
  · intro n j hs
    cases hr : R.out u (c n) with
    | none => rw [signalOf_none R u c n hr] at hs; cases hs
    | some r =>
      obtain ⟨j', hnj', _, hs'⟩ := hNamed n r hr
      rw [hs'] at hs
      cases hs
      exact hnj'
  · intro n hs
    apply (hAll n).1
    cases hr : R.out u (c (n + 1)) with
    | none => rfl
    | some r =>
      obtain ⟨_, _, _, hs'⟩ := hNamed (n + 1) r hr
      rw [hs'] at hs
      cases hs
  · intro n hIssue
    rw [signalOf_some R u c n _ ((hAll n).2.1 hIssue)]
    exact indexOn_eq c hInj n
  · intro n j hs
    cases hr : R.out u (c (n + 1)) with
    | none => rw [signalOf_none R u c (n + 1) hr] at hs; cases hs
    | some r =>
      rw [signalOf_some R u c (n + 1) r hr] at hs
      rw [signalOf_some R u c n r ((hAll n).2.2.1 r hr)]
      exact hs

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
  intro v hwv x t hx hCont hxt
  by_contra hNot
  obtain ⟨c, hc0, hDesc⟩ :=
    TruthCore.Results.Causality.ComingToBeHorns.descentOfNotAcc t hNot
  have hPop : PopulatedAt h Concrete v (c 0) := ⟨x, hx, hCont, hc0 ▸ hxt⟩
  obtain ⟨u, _, hAll⟩ :=
    hPatch v hwv c hDesc hPop (hPieces v hwv c hDesc hPop)
  exact arrangementImpossible R u c hDesc hAll

/-- A coinitial descent from `t` shows that the past of `t` has no beginning. -/
theorem notBegunOfCoinitial {T : Type} [Preorder T] (c : Nat → T)
    (hDesc : Descent c) (hCo : Coinitial c) : ¬ BegunAt (c 0) := by
  rintro ⟨m, hm, hMin⟩
  rcases hm with hm | hm
  · exact hMin (c 1) (hm ▸ hDesc 0)
  · obtain ⟨n, hn⟩ := hCo m hm
    exact hMin (c (n + 1)) (lt_trans (hDesc n) hn)

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
  intro v hwv x t hx hCont hxt
  by_contra hNot
  have hPopT : PopulatedAt h Concrete v t := ⟨x, hx, hCont, hxt⟩
  obtain ⟨c, hc0, hDesc, hCo⟩ := hCount v hwv t hPopT hNot
  have hPop : PopulatedAt h Concrete v (c 0) := hc0 ▸ hPopT
  obtain ⟨u, _, hAll⟩ :=
    hPatch v hwv c hDesc hCo hPop (hPieces v hwv c hDesc hCo hPop)
  exact arrangementImpossible R u c hDesc hAll

/-- In a history whose populated moments have begun pasts, if every contingent
concrete thing has an existing concrete ground and grounds precede what they
ground, every contingent concrete thing comes to be. -/
theorem comesToBeOfEarlierGroundsBegun {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (v : W)
    (hBegun : ∀ x t, Concrete x → ContingentAt h.ontic v x → h.IsAt v x t →
      BegunAt t)
    (hGrounded : TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨h.ontic, Concrete, grounds⟩ v)
    (hPrecede : GroundsPrecedeAt h Concrete grounds v) :
    AllContingentsComeToBeAt h Concrete v := by
  intro x hx hCont t hxt
  by_contra hNever
  have hAlways : ∀ s, s < t → h.IsAt v x s := by
    intro s hs
    by_contra hAbsent
    exact hNever ⟨s, hs, hAbsent⟩
  obtain ⟨m, hm, hMin⟩ := hBegun x t hx hCont hxt
  have hxm : h.IsAt v x m := by
    rcases hm with rfl | hm
    · exact hxt
    · exact hAlways m hm
  obtain ⟨y, _, _, hyx⟩ := hGrounded x hx hCont.1 hCont
  obtain ⟨s, hs, _⟩ := hPrecede x y m hx hCont hyx hxm
  exact hMin s hs

/-- Premise A3′w of the modal spine (possible begun coming-to-be) from begun
populated pasts and the possibility of a populated history whose contingent
concrete things all have earlier-present concrete grounds. -/
theorem possiblyBegunOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hPast : PopulatedPastsBegun h Concrete w)
    (hPossible : PossiblyEarlierGroundedPopulated h Concrete grounds w) :
    PossiblyBegunComingToBe h Concrete w := by
  obtain ⟨v, hwv, ⟨x, t, hx, hCont, hxt⟩, hGrounded, hPrecede⟩ := hPossible
  refine ⟨v, hwv, ?_, x, t, hx, hCont, hxt, hPast v hwv x t hx hCont hxt⟩
  exact comesToBeOfEarlierGroundsBegun h Concrete grounds v (hPast v hwv)
    hGrounded hPrecede

/-- Strength order: founded populated pasts give begun populated pasts. -/
theorem populatedPastsBegunOfFounded {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hFounded : PopulatedPastsFounded h Concrete w) :
    PopulatedPastsBegun h Concrete w :=
  fun v hwv x t hx hCont hxt =>
    TruthCore.Results.Causality.BegunComingToBe.begunOfAcc t
      (hFounded v hwv x t hx hCont hxt)

/-- Strength order: local pieces along every descent give local pieces along
every coinitial descent. -/
theorem coinitialPiecesOfPieces {W B T : Type} [Preorder T] (R : ReaperFrame W T)
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPieces : ReaperPiecesPossible R h Concrete w) :
    CoinitialReaperPiecesPossible R h Concrete w :=
  fun v hwv c hDesc _ hPop => hPieces v hwv c hDesc hPop

/-- Strength order: patchwork along every descent gives patchwork along every
coinitial descent. -/
theorem coinitialPatchworkOfPatchwork {W B T : Type} [Preorder T]
    (R : ReaperFrame W T) (h : History W B T) (Concrete : B → Prop) (w : W)
    (hPatch : ReaperPatchwork R h Concrete w) :
    CoinitialReaperPatchwork R h Concrete w :=
  fun v hwv c hDesc _ hPop => hPatch v hwv c hDesc hPop

open TruthCore.Causality.GrimReaperPatchwork.Control
open TruthCore.Causality.InertEmptiness.Control (all)
open TruthCore.Causality.BegunComingToBe.Control (zeno predecessorGrounds)

theorem pivotOne : (1 : Int) ≠ 0 := by decide

/-- In `pivot`, a contingent individual (`0`) is present at moment `0` of
world `1`. -/
theorem pivotPopulated : PopulatedAt pivot all 1 0 :=
  ⟨0, trivial, ⟨pivotOne, 0, trivial, fun h => h rfl⟩, pivotOne, le_refl _⟩

theorem pivotDescent : Descent (fun n : Nat => -(n : Int)) := by
  intro n; push_cast; omega

theorem pivotCoinitial : Coinitial (fun n : Nat => -(n : Int)) := by
  intro s hs
  refine ⟨(-s).toNat + 1, ?_⟩
  simp
  omega

theorem pivotNotBegun (t : Int) : ¬ BegunAt t := by
  rintro ⟨m, _, hMin⟩
  exact hMin (m - 1) (by omega)

theorem quietNoPiece {W T : Type} (u : W) (c : Nat → T) (n : Nat) :
    ¬ PieceAt (quietFrame W T) u c n :=
  fun hp => hp.1 rfl

/-- In world `c (n + 1)` of the pivot registers, the pieces of stations `n` and
`n + 1` both hold. -/
theorem pivotPieces (c : Nat → Int) (hDesc : Descent c) (n : Nat) :
    PieceAt pivotFrame (c (n + 1)) c n ∧ PieceAt pivotFrame (c (n + 1)) c (n + 1) := by
  have h1 := hDesc n
  have h2 := hDesc (n + 1)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro hn; simp [pivotFrame] at hn
  · intro hi; simp [pivotFrame] at hi; omega
  · intro r hr
    simp [pivotFrame] at hr ⊢
    exact ⟨by omega, hr⟩
  · intro r hr
    simp [pivotFrame] at hr
    exact ⟨n + 1, by omega, hr.2.symm⟩
  · intro _; simp [pivotFrame]
  · intro _; simp [pivotFrame]
  · intro r hr; simp [pivotFrame] at hr; omega
  · intro r hr
    simp [pivotFrame] at hr
    exact ⟨n + 1, le_refl _, hr.symm⟩

theorem pivotPiecesPossible : ReaperPiecesPossible pivotFrame pivot all 1 :=
  fun _ _ c hDesc _ n => ⟨c (n + 1), trivial, pivotPieces c hDesc n⟩

/-- In `zeno` no populated moment starts a coinitial descent: the first moment
`⊥` lies below it and nothing lies below `⊥`. -/
theorem zenoNoCoinitialAt (v : Bool) (c : Nat → WithBot Int) (_hDesc : Descent c)
    (hCo : Coinitial c) (hPop : PopulatedAt zeno all v (c 0)) : False := by
  obtain ⟨x, _, _, _, hx⟩ := hPop
  have hBot : (⊥ : WithBot Int) < c 0 :=
    lt_of_lt_of_le (WithBot.bot_lt_coe x) hx
  obtain ⟨n, hn⟩ := hCo ⊥ hBot
  exact absurd hn (not_lt_bot)

theorem zenoBegun : PopulatedPastsBegun zeno all true := by
  intro v _ x t _ _ hxt
  exact ⟨⊥, Or.inr (lt_of_lt_of_le (WithBot.bot_lt_coe x) hxt.2), fun r => not_lt_bot⟩

theorem zenoContingent (x : Int) : ContingentAt zeno.ontic true x :=
  ⟨rfl, false, trivial, Bool.false_ne_true⟩

theorem zenoNotFounded : ¬ PopulatedPastsFounded zeno all true := fun hF =>
  TruthCore.Results.Causality.BegunComingToBe.coeNotAcc 0
    (hF true trivial 0 ((0 : Int) : WithBot Int) trivial (zenoContingent 0)
      ⟨rfl, le_refl _⟩)

/-- Independence and nonvacuity controls. -/
theorem controls : TruthCore.Causality.GrimReaperPatchwork.Control.Certificate := by
  obtain ⟨hZenoPossible, _, _, _, hZenoNoNec, _, _⟩ :=
    TruthCore.Results.Causality.BegunComingToBe.controls
  have hPivotNotBegun : ¬ PopulatedPastsBegun pivot all 1 := fun hB =>
    pivotNotBegun 0 (hB 1 trivial 0 0 trivial
      ⟨pivotOne, 0, trivial, fun h => h rfl⟩ ⟨pivotOne, le_refl _⟩)
  have hPivotPatchFails : ¬ CoinitialReaperPatchwork pivotFrame pivot all 1 := by
    intro hPatch
    obtain ⟨u, _, hAll⟩ := hPatch 1 trivial _ pivotDescent pivotCoinitial
      pivotPopulated (pivotPiecesPossible 1 trivial _ pivotDescent pivotPopulated)
    exact arrangementImpossible pivotFrame u _ pivotDescent hAll
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hPivotNotBegun⟩,
    ⟨pivotPiecesPossible, coinitialPiecesOfPieces _ _ _ _ pivotPiecesPossible,
      fun h => hPivotPatchFails (coinitialPatchworkOfPatchwork _ _ _ _ h),
      hPivotPatchFails, hPivotNotBegun, ?_⟩,
    ⟨?_, ?_, ?_, zenoBegun, ?_, ?_, hZenoNoNec, ?_, ?_⟩⟩
  · intro _ _ c _ _ hAdj
    obtain ⟨_, _, hp, _⟩ := hAdj 0
    exact (quietNoPiece _ c 0 hp).elim
  · intro _ _ c _ _ _ hAdj
    obtain ⟨_, _, hp, _⟩ := hAdj 0
    exact (quietNoPiece _ c 0 hp).elim
  · intro hPieces
    obtain ⟨_, _, hp, _⟩ := hPieces 1 trivial _ pivotDescent pivotPopulated 0
    exact quietNoPiece _ _ 0 hp
  · intro hPieces
    obtain ⟨_, _, hp, _⟩ :=
      hPieces 1 trivial _ pivotDescent pivotCoinitial pivotPopulated 0
    exact quietNoPiece _ _ 0 hp
  · intro hF
    exact TruthCore.Results.Causality.ContingentComingToBe.intNotAcc 0
      (hF 1 trivial 0 0 trivial ⟨pivotOne, 0, trivial, fun h => h rfl⟩
        ⟨pivotOne, le_refl _⟩)
  · intro _ _ t _ _
    refine ⟨fun n => t - n, by simp, ?_, ?_⟩
    · intro n; push_cast; omega
    · intro s hs
      refine ⟨(t - s).toNat + 1, ?_⟩
      simp at hs ⊢
      omega
  · intro v _ c hDesc hCo hPop
    exact (zenoNoCoinitialAt v c hDesc hCo hPop).elim
  · intro v _ c hDesc hCo hPop
    exact (zenoNoCoinitialAt v c hDesc hCo hPop).elim
  · intro v _ t hPop hNot
    obtain ⟨x, _, _, _, hx⟩ := hPop
    exact (hNot ⟨⊥, Or.inr (lt_of_lt_of_le (WithBot.bot_lt_coe x) hx),
      fun r => not_lt_bot⟩).elim
  · refine ⟨true, trivial, ⟨0, (0 : Int), trivial, zenoContingent 0, rfl, le_refl _⟩,
      ?_, ?_⟩
    · intro x _ _ _
      exact ⟨x - 1, trivial, rfl, rfl, rfl⟩
    · intro x y t _ _ hyx hxt
      obtain ⟨_, rfl⟩ := hyx
      refine ⟨((x - 1 : Int) : WithBot Int), ?_, rfl, le_refl _⟩
      exact lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by omega)) hxt.2
  · exact hZenoPossible
  · exact zenoNotFounded
  · intro R ⟨hPieces, hPatch⟩
    exact zenoNotFounded (populatedPastsFoundedOfPatchwork R zeno all true hPieces hPatch)

end TruthCore.Results.Causality.GrimReaperPatchwork
