module

public import TruthCore.Causality.ComingToBeHorns
public import TruthCore.Results.Causality.ContingentComingToBe.Solution
public import TruthCore.Results.Causality.IndexedSignalReaper.Solution
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace TruthCore.Results.Causality.ComingToBeHorns
open TruthCore.Causality.ComingToBeHorns
open TruthCore.Causality.ContingentComingToBe
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Modal.TemporalHistory (History)
open TruthCore.Case.Catholicism.StageOne.CausalFinitism (FiniteDistinctAncestry)

/-- A moment without a founded past starts an endless strictly descending
sequence of moments (dependent choice, classical). -/
theorem descentOfNotAcc {T : Type} [Preorder T] (t : T)
    (hNot : ¬ Acc (fun a b : T => a < b) t) :
    ∃ c : Nat → T, c 0 = t ∧ ∀ n, c (n + 1) < c n := by
  classical
  have step : ∀ a : {a : T // ¬ Acc (fun a b : T => a < b) a},
      ∃ b : {a : T // ¬ Acc (fun a b : T => a < b) a}, b.1 < a.1 := by
    rintro ⟨a, ha⟩
    by_contra hNone
    apply ha
    refine Acc.intro a (fun b hb => ?_)
    by_contra hb'
    exact hNone ⟨⟨b, hb'⟩, hb⟩
  choose f hf using step
  let c : Nat → {a : T // ¬ Acc (fun a b : T => a < b) a} :=
    fun n => Nat.rec ⟨t, hNot⟩ (fun _ a => f a) n
  exact ⟨fun n => (c n).1, rfl, fun n => hf (c n)⟩

/-- A strictly descending sequence of a preorder takes its later values
strictly below its first value. -/
theorem descentBelow {T : Type} [Preorder T] (c : Nat → T)
    (hDesc : ∀ n, c (n + 1) < c n) : ∀ n, c (n + 1) < c 0 := by
  intro n
  induction n with
  | zero => exact hDesc 0
  | succ n ih => exact lt_trans (hDesc (n + 1)) ih

/-- A strictly descending sequence of a preorder never repeats a value. -/
theorem descentInjective {T : Type} [Preorder T] (c : Nat → T)
    (hDesc : ∀ n, c (n + 1) < c n) : Function.Injective c := by
  have hBelow : ∀ m k, c (m + k + 1) < c m := by
    intro m k
    induction k with
    | zero => exact hDesc m
    | succ k ih => exact lt_trans (hDesc (m + k + 1)) ih
  intro i j hij
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact absurd (hij ▸ hBelow i k) (lt_irrefl _)
  · exact heq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact absurd (hij ▸ hBelow j k) (lt_irrefl _)

/-- Horn H2 priced by the Grim Reaper results. Under the Reaper assembly
bridge, every populated moment of every accessible history has a founded past:
otherwise an endless descent below it would carry stations satisfying the four
local rules, which `IndexedSignalReaper.impossible` refutes. -/
theorem populatedPastsFoundedOfReaper {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (w : W)
    (hAssembly : ReaperAssembly h Concrete w) :
    PopulatedPastsFounded h Concrete w := by
  intro v hwv x t hx hCont hxt
  by_contra hNot
  obtain ⟨c, hc0, hDesc⟩ := descentOfNotAcc t hNot
  obtain ⟨signal, issued, hBound, hTrigger, hEmit, hForward⟩ :=
    hAssembly v hwv c hDesc ⟨x, hx, hCont, hc0 ▸ hxt⟩
  exact TruthCore.Results.Causality.IndexedSignalReaper.impossible
    signal issued hBound hTrigger hEmit hForward

/-- Horn H2 priced by causal finitism. If the momentary states of each
accessible history have finitely many causal ancestors, and every earlier
state is a causal ancestor of the state at a populated moment, every populated
moment has a founded past: an endless descent below it would give infinitely
many distinct ancestors. No-loops is not needed: the strict temporal order
already makes the descending moments distinct. -/
theorem populatedPastsFoundedOfStateFinitism {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (stateCause : W → T → T → Prop)
    (w : W)
    (hFinite : StateCausalFinitism h stateCause w)
    (hBridge : PrecedenceIsStateCausation h Concrete stateCause w) :
    PopulatedPastsFounded h Concrete w := by
  intro v hwv x t hx hCont hxt
  by_contra hNot
  obtain ⟨c, hc0, hDesc⟩ := descentOfNotAcc t hNot
  have hInj : Function.Injective (fun n => c (n + 1)) :=
    fun i j hij => Nat.succ_injective (descentInjective c hDesc hij)
  have hMem : ∀ n, c (n + 1) ∈ {s | Relation.TransGen (stateCause v) s t} := by
    intro n
    exact hBridge v hwv x t (c (n + 1)) hx hCont hxt (hc0 ▸ descentBelow c hDesc n)
  exact Set.infinite_of_injective_forall_mem hInj hMem (hFinite v hwv t)

/-- Horn H1 priced by the grounding premise. In a history whose populated
moments have founded pasts, if every contingent concrete thing has an existing
concrete ground and grounds precede what they ground, every contingent concrete
thing comes to be: a thing present at all moments below a founded moment would
be present at a moment with nothing earlier, where its ground could not be. -/
theorem comesToBeOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (v : W)
    (hFounded : ∀ x t, Concrete x → ContingentAt h.ontic v x → h.IsAt v x t →
      Acc (fun a b : T => a < b) t)
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
  obtain ⟨m, hm, hMin⟩ :=
    TruthCore.Results.Causality.ContingentComingToBe.minimalBelow t
      (hFounded x t hx hCont hxt)
  have hxm : h.IsAt v x m := by
    rcases hm with rfl | hm
    · exact hxt
    · exact hAlways m hm
  obtain ⟨y, _, _, hyx⟩ := hGrounded x hx hCont.1 hCont
  obtain ⟨s, hs, _⟩ := hPrecede x y m hx hCont hyx hxm
  exact hMin s hs

/-- Premise A3′ of the modal spine from founded populated pasts and the
possibility of a populated history whose contingent concrete things all have
earlier-present concrete grounds. -/
theorem possiblyFoundedOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hPast : PopulatedPastsFounded h Concrete w)
    (hPossible : PossiblyEarlierGroundedPopulated h Concrete grounds w) :
    PossiblyFoundedComingToBe h Concrete w := by
  obtain ⟨v, hwv, ⟨x, t, hx, hCont, hxt⟩, hGrounded, hPrecede⟩ := hPossible
  refine ⟨v, hwv, ?_, x, t, hx, hCont, hxt, hPast v hwv x t hx hCont hxt⟩
  exact comesToBeOfEarlierGrounds h Concrete grounds v (hPast v hwv) hGrounded hPrecede

/-- The A3′ support bundle already contains the possibility of a necessary
concrete being. In the witnessing history, a present contingent thing has a
ground present strictly earlier; if that ground is contingent, repeat. The
descent runs along the founded past of the first moment, so it stops at a
ground that is not contingent: a concrete individual existing in that history
and in every history accessible from it. -/
theorem possiblyNecessaryOfEarlierGrounds {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop) (grounds : W → B → B → Prop) (w : W)
    (hPast : PopulatedPastsFounded h Concrete w)
    (hPossible : PossiblyEarlierGroundedPopulated h Concrete grounds w) :
    PossiblyNecessaryConcrete h Concrete grounds w := by
  classical
  obtain ⟨v, hwv, ⟨x, t, hx, hCont, hxt⟩, hGrounded, hPrecede⟩ := hPossible
  refine ⟨v, hwv, ?_⟩
  have descend : ∀ t, Acc (fun a b : T => a < b) t → ∀ x, Concrete x →
      ContingentAt h.ontic v x → h.IsAt v x t →
      TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
        ⟨h.ontic, Concrete, grounds⟩ v := by
    intro t hAcc
    induction hAcc with
    | intro t _ ih =>
      intro x hx hCont hxt
      obtain ⟨y, hy, hyExists, hyx⟩ := hGrounded x hx hCont.1 hCont
      obtain ⟨s, hs, hys⟩ := hPrecede x y t hx hCont hyx hxt
      by_cases hyCont : ContingentAt h.ontic v y
      · exact ih s hs y hy hyCont hys
      · refine ⟨y, hy, hyExists, fun u hu => ?_⟩
        by_contra hAbsent
        exact hyCont ⟨hyExists, u, hu, hAbsent⟩
  exact descend t (hPast v hwv x t hx hCont hxt) x hx hCont hxt

/-- No strictly descending sequence of natural numbers. -/
theorem natNoDescent (c : Nat → Nat) (hDesc : ∀ n, c (n + 1) < c n) : False := by
  have hBound : ∀ n, c n + n ≤ c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hDesc n; omega
  have := hBound (c 0 + 1)
  omega

/-- Every natural-number moment has a founded past. -/
theorem natAcc (t : Nat) : Acc (fun a b : Nat => a < b) t :=
  (wellFounded_lt (α := Nat)).apply t

open TruthCore.Causality.ComingToBeHorns.Control
open TruthCore.Causality.ContingentComingToBe.Control (endless)
open TruthCore.Causality.InertEmptiness.Control (all rooted)

/-- No positive moment of dense time has a founded past: `t / 2` lies below `t`. -/
theorem denseNotAcc (t : DenseTime) (hPos : 0 < t.1) :
    ¬ Acc (fun a b : DenseTime => a < b) t := by
  intro hAcc
  induction hAcc with
  | intro t _ ih =>
    have hHalf : 0 ≤ t.1 / 2 := by linarith
    exact ih ⟨t.1 / 2, hHalf⟩ (show t.1 / 2 < t.1 by linarith)
      (show (0 : ℚ) < t.1 / 2 by linarith)

/-- Control (7): later grounding. -/
theorem laterGroundControl :
    PopulatedPastsFounded laterGround all true ∧
    TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt
      ⟨laterGround.ontic, all, mutualGrounds⟩ true ∧
    ¬ GroundsPrecedeAt laterGround all mutualGrounds true ∧
    ¬ AllContingentsComeToBeAt laterGround all true ∧
    (∀ x y t, mutualGrounds true y x →
      ¬ (laterGround.IsAt true x t ∧ laterGround.IsAt true y t)) ∧
    ¬ TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt
      ⟨laterGround.ontic, all, mutualGrounds⟩ true := by
  have laterCont : ∀ x : Bool, ContingentAt laterGround.ontic true x :=
    fun _ => ⟨rfl, false, trivial, Bool.false_ne_true⟩
  refine ⟨fun _ _ _ t _ _ _ => natAcc t, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ hEx _
    refine ⟨!x, trivial, hEx, ?_⟩
    cases x <;> simp [mutualGrounds]
  · intro hPrecede
    obtain ⟨s, hs, _⟩ := hPrecede false true 0 trivial (laterCont false)
      (by simp [mutualGrounds]) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    exact Nat.not_lt_zero s hs
  · intro hCome
    obtain ⟨s, hs, _⟩ := hCome false trivial (laterCont false) 0 ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    exact Nat.not_lt_zero s hs
  · intro x y t hyx ⟨⟨_, hx⟩, ⟨_, hy⟩⟩
    cases x <;> cases y <;> simp_all [mutualGrounds]
  · rintro ⟨x, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial)

/-- Control (8): dense time with a first moment. -/
theorem densePastControl :
    (∀ s : DenseTime, ¬ s < denseZero) ∧
    TruthCore.Causality.CountTemporalNecessity.HistoryPresenceActual densePast ∧
    EmptinessStaysEmpty densePast all ∧
    AllContingentsComeToBeAt densePast all true ∧
    TruthCore.Causality.InertEmptiness.PossiblyContingentsAbsentThenPresent
      densePast all true ∧
    ¬ PopulatedPastsFounded densePast all true ∧
    ¬ PossiblyFoundedComingToBe densePast all true ∧
    ¬ ReaperAssembly densePast all true ∧
    ∀ stateCause : Bool → DenseTime → DenseTime → Prop,
      ¬ (StateCausalFinitism densePast stateCause true ∧
        PrecedenceIsStateCausation densePast all stateCause true) := by
  have denseCont : ContingentAt densePast.ontic true true :=
    ⟨Or.inr rfl, false, trivial, by rintro (h | h) <;> cases h⟩
  have contTrue : ∀ v x, ContingentAt densePast.ontic v x → x = true ∧ v = true := by
    intro v x hCont
    obtain ⟨hEx, u, _, hAbsent⟩ := hCont
    cases x
    · exact (hAbsent (Or.inl rfl)).elim
    · rcases hEx with h | h
      · cases h
      · exact ⟨rfl, h⟩
  let one : DenseTime := ⟨1, by norm_num⟩
  have notFounded : ¬ PopulatedPastsFounded densePast all true := fun hPast =>
    denseNotAcc one (by norm_num [one])
      (hPast true trivial true one trivial denseCont (Or.inr ⟨rfl, by norm_num [one]⟩))
  refine ⟨fun s hs => ?_, ?_, ?_, ?_, ?_, notFounded, ?_, ?_, ?_⟩
  · have h0 : s.1 < 0 := hs
    linarith [s.2]
  · intro v x t hp
    rcases hp with hp | ⟨hp, _⟩
    · exact Or.inl hp
    · exact Or.inr hp
  · intro v s t _ hEmpty x _ _
    exact hEmpty false trivial (Or.inl rfl)
  · intro x _ hCont t hxt
    obtain ⟨rfl, _⟩ := contTrue true x hCont
    rcases hxt with hxt | ⟨_, hPos⟩
    · cases hxt
    · refine ⟨denseZero, show (0 : ℚ) < t.1 from hPos, ?_⟩
      rintro (h | ⟨_, h⟩)
      · cases h
      · exact lt_irrefl _ h
  · refine ⟨true, trivial, denseZero, one, show (0 : ℚ) < 1 by norm_num, ?_,
      true, trivial, denseCont, Or.inr ⟨rfl, by norm_num [one]⟩⟩
    intro x _ hCont hx
    obtain ⟨rfl, _⟩ := contTrue true x hCont
    rcases hx with h | ⟨_, h⟩
    · cases h
    · exact lt_irrefl _ h
  · rintro ⟨v, _, _, x, t, _, hCont, hxt, hAcc⟩
    obtain ⟨rfl, rfl⟩ := contTrue v x hCont
    rcases hxt with h | ⟨_, hPos⟩
    · cases h
    · exact denseNotAcc t hPos hAcc
  · intro hAssembly
    exact notFounded (populatedPastsFoundedOfReaper densePast all true hAssembly)
  · rintro stateCause ⟨hFinite, hBridge⟩
    exact notFounded
      (populatedPastsFoundedOfStateFinitism densePast all stateCause true hFinite hBridge)

/-- Omission and nonvacuity controls. -/
theorem controls : TruthCore.Causality.ComingToBeHorns.Control.Certificate := by
  -- contingency at world `true` of the endless control
  have endlessCont : ∀ x : Int, ContingentAt endless.ontic true x :=
    fun _ => ⟨rfl, false, trivial, Bool.false_ne_true⟩
  have endlessUnfounded : ¬ PopulatedPastsFounded endless all true := fun hPast =>
    TruthCore.Results.Causality.ContingentComingToBe.intNotAcc 0
      (hPast true trivial 0 0 trivial (endlessCont 0) ⟨rfl, le_refl 0⟩)
  have endlessNotPossible : ¬ PossiblyFoundedComingToBe endless all true := by
    rintro ⟨v, _, _, x, t, _, _, _, hAcc⟩
    exact TruthCore.Results.Causality.ContingentComingToBe.intNotAcc t hAcc
  have sustainedCont : ContingentAt sustained.ontic true true :=
    ⟨Or.inr rfl, false, trivial, by rintro (h | h) <;> cases h⟩
  have rootedCont : ContingentAt rooted.ontic true true :=
    ⟨Or.inr rfl, false, trivial, by rintro (h | h) <;> cases h⟩
  have cycleCont : ∀ x : Bool, ContingentAt cycle.ontic true x :=
    fun _ => ⟨rfl, false, trivial, Bool.false_ne_true⟩
  refine ⟨⟨?_, ?_, endlessUnfounded⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, endlessNotPossible⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, laterGroundControl, densePastControl⟩
  -- (1) idle states
  · intro v _ t
    refine Set.Finite.subset Set.finite_empty ?_
    intro s hs
    cases hs with
    | single hEdge => exact hEdge.elim
    | tail _ hEdge => exact hEdge.elim
  · intro hBridge
    have := hBridge true trivial 0 0 (-1) trivial (endlessCont 0) ⟨rfl, le_refl 0⟩
      (by decide)
    cases this with
    | single hEdge => exact hEdge
    | tail _ hEdge => exact hEdge
  -- (2) every earlier state causes every later one
  · intro v _ x t s _ _ _ hst
    exact Relation.TransGen.single hst
  · intro hFinite
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : Nat => -(n : Int) - 1) (fun i j hij => by simp at hij; omega)
      (fun n => ?_) (hFinite true trivial 0)
    exact Relation.TransGen.single (show -(n : Int) - 1 < 0 by omega)
  · intro hAssembly
    obtain ⟨signal, issued, hBound, hTrigger, hEmit, hForward⟩ :=
      hAssembly true trivial (fun n => -(n : Int)) (fun n => by omega)
        ⟨0, trivial, endlessCont 0, rfl, le_refl 0⟩
    exact TruthCore.Results.Causality.IndexedSignalReaper.impossible
      signal issued hBound hTrigger hEmit hForward
  -- (3) predecessors ground
  · intro x _ _ _
    exact ⟨x - 1, trivial, rfl, rfl⟩
  · intro x y t _ _ hyx hxt
    refine ⟨t - 1, by omega, hxt.1, ?_⟩
    change y = x - 1 at hyx
    have := hxt.2
    omega
  -- (4) simultaneous sustaining
  · intro v _ x t _ _ _
    exact natAcc t
  · intro x _ _ hCont
    refine ⟨false, trivial, Or.inl rfl, rfl, ?_⟩
    cases x
    · obtain ⟨_, u, _, hAbsent⟩ := hCont
      exact (hAbsent (Or.inl rfl)).elim
    · rfl
  · intro hPrecede
    obtain ⟨s, hs, _⟩ := hPrecede true false 0 trivial
      sustainedCont ⟨rfl, rfl⟩ (Or.inr rfl)
    exact Nat.not_lt_zero s hs
  · intro hCome
    obtain ⟨s, hs, _⟩ := hCome true trivial sustainedCont 0
      (Or.inr rfl)
    exact Nat.not_lt_zero s hs
  · rintro ⟨v, _, hCome, x, t, _, hCont, hxt, _⟩
    cases x
    · obtain ⟨_, u, _, hAbsent⟩ := hCont
      exact hAbsent (Or.inl rfl)
    · cases v
      · obtain ⟨hEx, _⟩ := hCont
        simp [sustained] at hEx
      · obtain ⟨s, hs, _⟩ := hCome true trivial hCont 0 (Or.inr rfl)
        exact Nat.not_lt_zero s hs
  · exact ⟨false, trivial, Or.inl rfl, fun _ _ => Or.inl rfl⟩
  -- (5) mutual simultaneous grounding
  · intro v _ x t _ _ _
    exact natAcc t
  · intro v x t hp
    exact hp
  · intro v s t _ hEmpty x _ hxt
    exact hEmpty x trivial hxt
  · intro x _ hEx _
    refine ⟨!x, trivial, hEx, ?_⟩
    cases x <;> simp [mutualGrounds]
  · intro hPrecede
    obtain ⟨s, hs, _⟩ := hPrecede true false 0 trivial
      (cycleCont false) Bool.false_ne_true rfl
    exact Nat.not_lt_zero s hs
  · intro hCome
    obtain ⟨s, hs, _⟩ := hCome true trivial (cycleCont false) 0 rfl
    exact Nat.not_lt_zero s hs
  · rintro ⟨v, _, hCome, x, t, _, hCont, hxt, _⟩
    cases v
    · exact absurd hCont.1 Bool.false_ne_true
    · obtain ⟨s, hs, _⟩ := hCome true trivial (cycleCont false) 0 rfl
      exact Nat.not_lt_zero s hs
  · rintro ⟨x, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial)
  · intro hWF
    have hLoop : ∀ x : Bool, ¬ Acc (mutualGrounds true) x := by
      intro x hAcc
      induction hAcc with
      | intro x _ ih => exact ih (!x) (by cases x <;> simp [mutualGrounds])
    exact hLoop true (hWF.apply true)
  -- (6) rooted joint witness
  · intro v _ c hDesc _
    exact (natNoDescent c hDesc).elim
  · intro v _ t
    have hEq : {s | Relation.TransGen (natPrecedenceStates v) s t} = Set.Iio t := by
      ext s
      change Relation.TransGen (fun a b : Nat => a < b) s t ↔ s < t
      rw [Relation.transGen_eq_self]
    rw [hEq]
    exact Set.finite_Iio t
  · intro v _ x t s _ _ _ hst
    exact Relation.TransGen.single hst
  · intro v _ x t _ _ _
    exact natAcc t
  · refine ⟨true, trivial, ⟨true, 1, trivial, rootedCont,
      Or.inr ⟨rfl, rfl⟩⟩, ?_, ?_⟩
    · intro x _ _ hCont
      refine ⟨false, trivial, Or.inl rfl, rfl, ?_⟩
      cases x
      · obtain ⟨_, u, _, hAbsent⟩ := hCont
        exact (hAbsent (Or.inl rfl)).elim
      · rfl
    · intro x y t _ _ hyx hxt
      obtain ⟨rfl, rfl⟩ := hyx
      rcases hxt with hxt | ⟨_, rfl⟩
      · exact absurd hxt (by decide)
      · exact ⟨0, by decide, Or.inl rfl⟩
  · exact (TruthCore.Results.Causality.ContingentComingToBe.controls).2.2

end TruthCore.Results.Causality.ComingToBeHorns
