import TruthCore.Causality.ComprehensionByMeasure

/-! Comprehension by measure: the q.12 a.7 bridge `bbac932e` (no intellect that
is not INFINITE_1 comprehends an INFINITE_1 being) derived from a degree of act,
a degree of knowability and a degree of knowing, through the COMPREHEND_2 sense
and one sense bridge from the primitive COMPREHEND_1. Analyst formulations,
attribution deferred. No premise is established. -/

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
    InfiniteIsMaximallyKnowable Infinite M := by
  sorry

/-- Every intellect that is not INFINITE_1 has a power of knowing bounded by a
non-maximal degree: its own degree of act, which bounds its knowing and is not
maximal. -/
theorem nonInfiniteIntellectHasNonMaximalPower {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (M : Measures Being Deg)
    (hNotMax : NonInfiniteActIsNotMaximal Infinite M) (hWithin : KnowingWithinKnowersAct M) :
    NonInfiniteIntellectHasNonMaximalPower Infinite HasIntellect M := by
  sorry

/-- No intellect that is not INFINITE_1 COMPREHEND_2s an INFINITE_1 being. If it
did, at a degree d, then for its power bound p: every degree is at most the
knowability of g (maximal), which is at most d, which is at most p; so p would be
maximal, against its bound being non-maximal. -/
theorem finiteIntellectDoesNotComprehend2Infinite {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (M : Measures Being Deg)
    (hKnowable : InfiniteIsMaximallyKnowable Infinite M)
    (hPower : NonInfiniteIntellectHasNonMaximalPower Infinite HasIntellect M) :
    FiniteIntellectDoesNotComprehend2Infinite Infinite HasIntellect M := by
  sorry

/-- The bridge `bbac932e` for the primitive COMPREHEND_1: a non-INFINITE_1
intellect that comprehended an INFINITE_1 being in the primitive sense would,
by the sense bridge, COMPREHEND_2 it, which the COMPREHEND_2 bridge excludes. -/
theorem finiteIntellectDoesNotComprehendInfiniteByMeasure {Being Deg : Type} [Preorder Deg]
    (Infinite HasIntellect : Being → Prop) (C : Comprehension Being) (M : Measures Being Deg)
    (hMeasured : FiniteIntellectDoesNotComprehend2Infinite Infinite HasIntellect M)
    (hSense : Comprehend1IsComprehend2 C M) :
    FiniteIntellectDoesNotComprehendInfinite Infinite HasIntellect C := by
  sorry

open Control in
/-- The controls of `ComprehensionByMeasure`, checked by case analysis on `Bool`. -/
theorem controls : Control.Controls := by
  sorry

end TruthCore.Results.Causality.ComprehensionByMeasure
