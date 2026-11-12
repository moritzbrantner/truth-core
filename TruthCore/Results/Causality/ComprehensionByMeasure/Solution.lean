module

public import TruthCore.Causality.ComprehensionByMeasure

/-! Comprehension by measure: the q.12 a.7 bridge `bbac932e` (no intellect that
is not INFINITE_1 comprehends an INFINITE_1 being) derived from a degree of act,
a degree of knowability and a degree of knowing, through the COMPREHEND_2 sense
and one sense bridge from the primitive COMPREHEND_1. Analyst formulations,
attribution deferred. No premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.ComprehensionByMeasure

open TruthCore.Causality.DeiFiliusImmenseIncomprehensible
  (Comprehension FiniteIntellectDoesNotComprehendInfinite)
open TruthCore.Causality.ComprehensionByMeasure

/-- Whatever is INFINITE_1 is maximally knowable: its degree of act is maximal,
and its knowability is at least its degree of act, so every degree is at most
its knowability. -/
theorem infiniteIsMaximallyKnowable {Being Deg : Type} [Preorder Deg]
    (Infinite : Being → Prop) (M : Measures Being Deg)
    (hAct : InfiniteActIsMaximal Infinite M) (hKnow : KnowableInsofarAsInAct M) :
    InfiniteIsMaximallyKnowable Infinite M :=
  fun g hg b => le_trans (hAct g hg b) (hKnow g)

/-- Every intellect that is not INFINITE_1 has a power of knowing bounded by a
non-maximal degree: its own degree of act, which bounds its knowing and is not
maximal. -/
theorem nonInfiniteIntellectHasNonMaximalPower {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (M : Measures Being Deg)
    (hNotMax : NonInfiniteActIsNotMaximal Infinite M) (hWithin : KnowingWithinKnowersAct M) :
    NonInfiniteIntellectHasNonMaximalPower Infinite HasIntellect M :=
  fun x _ hx => ⟨M.actDegree x, hNotMax x hx, hWithin x⟩

/-- No intellect that is not INFINITE_1 COMPREHEND_2s an INFINITE_1 being. If it
did, at a degree d, then for its power bound p: every degree is at most the
knowability of g (maximal), which is at most d, which is at most p; so p would be
maximal, against its bound being non-maximal. -/
theorem finiteIntellectDoesNotComprehend2Infinite {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (M : Measures Being Deg)
    (hKnowable : InfiniteIsMaximallyKnowable Infinite M)
    (hPower : NonInfiniteIntellectHasNonMaximalPower Infinite HasIntellect M) :
    FiniteIntellectDoesNotComprehend2Infinite Infinite HasIntellect M := by
  intro g x hg hx hfin ⟨d, hk, hle⟩
  obtain ⟨p, hp, hb⟩ := hPower x hx hfin
  exact hp fun b => le_trans (le_trans (hKnowable g hg b) hle) (hb g d hk)

/-- The bridge `bbac932e` for the primitive COMPREHEND_1: a non-INFINITE_1
intellect that comprehended an INFINITE_1 being in the primitive sense would,
by the sense bridge, COMPREHEND_2 it, which the COMPREHEND_2 bridge excludes. -/
theorem finiteIntellectDoesNotComprehendInfiniteByMeasure {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (C : Comprehension Being) (M : Measures Being Deg)
    (hMeasured : FiniteIntellectDoesNotComprehend2Infinite Infinite HasIntellect M)
    (hSense : Comprehend1IsComprehend2 C M) :
    FiniteIntellectDoesNotComprehendInfinite Infinite HasIntellect C :=
  fun g x hg hx hfin hc => hMeasured g x hg hx hfin (hSense x g hc)

open Control in
/-- The controls of `ComprehensionByMeasure`, checked by case analysis on `Bool`. -/
theorem controls : Control.Controls := by
  have topTrue : IsTop true := fun b => by cases b <;> decide
  have notTopFalse : ¬ IsTop false := fun h => absurd (h true) (by decide)
  have exactPrem : InfiniteActIsMaximal inf exact ∧ KnowableInsofarAsInAct exact ∧
      NonInfiniteActIsNotMaximal inf exact ∧ KnowingWithinKnowersAct exact := by
    refine ⟨fun g hg => ?_, fun _ => le_refl _, fun x hx => ?_, fun x _ d hd => ?_⟩
    · cases hg; exact topTrue
    · cases x
      · exact notTopFalse
      · exact absurd rfl hx
    · cases hd; exact le_refl _
  obtain ⟨e1, e2, e3, e4⟩ := exactPrem
  have exactMeasured : FiniteIntellectDoesNotComprehend2Infinite inf yes exact :=
    finiteIntellectDoesNotComprehend2Infinite inf yes exact
      (infiniteIsMaximallyKnowable inf exact e1 e2)
      (nonInfiniteIntellectHasNonMaximalPower inf yes exact e3 e4)
  have falseTrue : ∀ M : Measures Bool Bool, M.knowability true = false → M.KnowsAt false true false →
      ComprehendsByMeasure M false true := fun M hk hd => ⟨false, hd, by rw [hk]⟩
  refine ⟨⟨e1, e2, e3, e4, fun _ _ h => h, ?_, ⟨true, rfl, le_refl _⟩, ⟨false, rfl, le_refl _⟩⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, falseTrue flat rfl rfl⟩,
    ⟨?_, ?_, ?_, ?_, falseTrue lowKnowability rfl rfl⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨true, rfl, le_refl _⟩⟩,
    ⟨?_, ?_, ?_, ?_, ⟨true, rfl, le_refl _⟩⟩,
    ⟨exactMeasured, ?_, ?_⟩, ⟨fun _ _ h => h.elim, ?_⟩, ?_⟩
  -- 1. nonvacuity: the bridge itself
  · exact finiteIntellectDoesNotComprehendInfiniteByMeasure inf yes _ exact exactMeasured
      (fun _ _ h => h)
  -- 2. flat
  · exact fun h => notTopFalse (h true rfl)
  · exact fun _ => le_refl _
  · exact fun _ _ => notTopFalse
  · intro x _ d hd; cases hd; exact le_refl _
  · exact fun h => notTopFalse (h true rfl)
  · exact fun x _ _ => ⟨false, notTopFalse, fun _ d hd => by cases hd; exact le_refl _⟩
  -- 3. lowKnowability
  · intro g hg; cases hg; exact topTrue
  · exact fun h => absurd (h true) (by decide)
  · intro x hx; cases x
    · exact notTopFalse
    · exact absurd rfl hx
  · intro x _ d hd; cases hd; exact le_refl _
  -- 4. high
  · exact fun _ _ => topTrue
  · exact fun _ => le_refl _
  · exact fun h => h false Bool.false_ne_true topTrue
  · intro x _ d hd; cases hd; exact le_refl _
  · exact fun _ _ => topTrue
  · intro h
    obtain ⟨p, hp, hb⟩ := h false trivial Bool.false_ne_true
    exact hp fun b => le_trans (topTrue b) (hb true true rfl)
  -- 5. overreach
  · intro g hg; cases hg; exact topTrue
  · exact fun _ => le_refl _
  · intro x hx; cases x
    · exact notTopFalse
    · exact absurd rfl hx
  · exact fun h => absurd (h false true true rfl) (by decide)
  -- 6. the sense bridge is needed
  · intro h
    obtain ⟨d, hd, hle⟩ := h false true trivial
    cases hd
    exact absurd hle (by decide)
  · exact fun h => h true false rfl trivial Bool.false_ne_true trivial
  -- 7. the senses are not identified
  · exact fun h => h true true ⟨true, rfl, le_refl _⟩
  -- 8. scale commitment
  · intro B D _ _ Infinite M hAct g hg
    obtain ⟨b, hb⟩ := exists_gt (M.actDegree g)
    exact not_le_of_gt hb (hAct g hg b)

end TruthCore.Results.Causality.ComprehensionByMeasure
