module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia

/-! Analyst interpretation of DEF-GREATEST-CONCEIVABLE-BEING, attribution deferred.
Possible thought situations are not actual episodes or metaphysically possible worlds.
`Denotes` is intentional reference, never realization/existence. Neither a total
order nor the possibility of realizing a concept is implicit. The root connection
is the explicit bridge to IsMaximalIn at esse, not an ontological existence proof. -/

@[expose] public section
namespace TruthCore.Causality.ConceivableGreatness

universe u v w

/-- Open dictionaries: accessible thought situations, capacity to entertain a
concept there, intentional reference, and comparative greatness of the objects
as conceived. None is an opaque predicate for the whole target description. -/
structure Thought (Situation : Type u) (Concept : Type v) (Being : Type w) where
  Accessible : Situation → Situation → Prop
  CanEntertain : Situation → Concept → Prop
  Denotes : Concept → Being → Prop
  Greater : Being → Being → Prop

/-- Potential conceptualization, with explicit witnesses. This does not assert
an actual thinking episode, an actual being, or a realizable concept. -/
def Conceivable {S : Type u} {C : Type v} {B : Type w}
    (T : Thought S C B) (s : S) (b : B) : Prop :=
  ∃ t c, T.Accessible s t ∧ T.CanEntertain t c ∧ T.Denotes c b

/-- A conceivable intentional object than which no greater can be conceived.
Own conceivability rules out the empty-thought vacuity; the comparison clause is
no-greater, not dominance over incomparable objects. -/
def NoGreaterConceivable {S : Type u} {C : Type v} {B : Type w}
    (T : Thought S C B) (s : S) (b : B) : Prop :=
  Conceivable T s b ∧ ∀ x, Conceivable T s x → ¬ T.Greater x b

/-- Conditional passage to the EXACT existing merely-maximal predicate.
Coverage is needed for every competitor admitted by MoreIn, even if it is not
actual: IsMaximalIn's comparison clause has no actuality guard. Order alignment
is only in the direction required. Actual possession of r is a separate input. -/
theorem toMaximal {S : Type u} {C : Type v} {B : Type w} {R : Type}
    (T : Thought S C B) (s : S) (b : B)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (r : R)
    (h : NoGreaterConceivable T s b) (actual : InAct b r)
    (coverage : ∀ x, MoreIn r x b → Conceivable T s x)
    (alignment : ∀ x, MoreIn r x b → T.Greater x b) :
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn InAct MoreIn r b := by
  exact ⟨actual, fun x hx => h.2 x (coverage x hx) (alignment x hx)⟩

/-- Nonvacuity and incomparability: both objects are conceivable, neither is
greater; no-greater does not imply strict dominance or uniqueness. -/
theorem incomparableControl :
    let T : Thought Unit Bool Bool := ⟨fun _ _ => True, fun _ _ => True,
      fun c b => c = b, fun _ _ => False⟩
    NoGreaterConceivable T () false ∧ NoGreaterConceivable T () true ∧
      ¬ T.Greater false true := by
  simp [NoGreaterConceivable, Conceivable]
  <;> decide

/-- With no accessible thought situation even the candidate is not conceivable. -/
theorem vacuityControl :
    let T : Thought Unit Unit Unit := ⟨fun _ _ => False, fun _ _ => True,
      fun _ _ => True, fun _ _ => False⟩
    (∀ x, Conceivable T () x → ¬ T.Greater x ()) ∧
      ¬ NoGreaterConceivable T () () := by
  simp [NoGreaterConceivable, Conceivable]
  <;> decide

/-- Omit coverage: a greater competitor lies outside the thought scope. -/
theorem coverageControl :
    let T : Thought Unit Bool Bool := ⟨fun _ _ => True, fun _ c => c = false,
      fun c b => c = b, fun x b => x = true ∧ b = false⟩
    NoGreaterConceivable T () false ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn
        (fun _ _ : Bool => True) (fun _ x b => T.Greater x b) false false := by
  simp [NoGreaterConceivable, Conceivable,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn]
  <;> decide

/-- Omit alignment: actual comparison and conceptual comparison disagree. -/
theorem alignmentControl :
    let T : Thought Unit Bool Bool := ⟨fun _ _ => True, fun _ _ => True,
      fun c b => c = b, fun _ _ => False⟩
    NoGreaterConceivable T () false ∧ (∀ x, Conceivable T () x) ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn
        (fun _ _ : Bool => True) (fun _ x b => x = true ∧ b = false) false false := by
  simp [NoGreaterConceivable, Conceivable,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn]
  <;> decide

/-- Own conceptualization, coverage and alignment do not supply actuality. -/
theorem actualityControl :
    let T : Thought Unit Unit Unit := ⟨fun _ _ => True, fun _ _ => True,
      fun _ _ => True, fun _ _ => False⟩
    NoGreaterConceivable T () () ∧
      ¬ TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn
        (fun _ _ : Unit => False) (fun _ _ _ => False) () () := by
  simp [NoGreaterConceivable, Conceivable,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximalIn,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn]
  <;> decide

end TruthCore.Causality.ConceivableGreatness
