module
public import TruthCore.Causality.EternityDefinitionFork
public import TruthCore.Modal.TemporalHistory

@[expose] public section
namespace TruthCore.Causality.TemporalCoverageEternity
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Modal.TemporalHistory

/-- Finite comparison paths. Reverse edges are allowed because boundary absence
preserves an iff, not merely forward persistence. No order laws are imposed. -/
inductive Path {T : Type} [LT T] : T → T → Prop where
  | refl (s) : Path s s
  | step {s t u} : Path s t → (t < u ∨ u < t) → Path s u

/-- Coverage concerns only actual admitted comparisons; no life predicate occurs. -/
def Covered {T : Type} [LT T] (anchor : T) : Prop := ∀ t, Path anchor t

def Transport : Prop := ∀ (B T : Type) [LT T] (l : B → T → Prop) x s,
  Interminable l x → l x s → ∀ t, Path s t → l x t

/-- Selected being/world only: no converse or global ontology calibration. -/
def LifeToBeing {W B T : Type} (h : History W B T) (w : W)
    (l : B → T → Prop) (x : B) : Prop := ∀ t, l x t → h.IsAt w x t

def Consumer : Prop := ∀ (W B T : Type) [LT T] (h : History W B T)
    (w : W) (l : B → T → Prop) x s,
  Covered s → Interminable l x → l x s → LifeToBeing h w l x → EverlastingAt h w x

local instance : LT Unit := ⟨fun _ _ => False⟩

/-- Formal omission and nonvacuity tests; not claims of metaphysical possibility. -/
def Controls : Prop :=
  (∃ (l : Unit → Bool → Prop), l () true ∧
    @Interminable Unit Bool ⟨fun _ _ => False⟩ l () ∧ ¬ l () false) ∧
  (∃ (h : History Unit Unit Unit) (l : Unit → Unit → Prop),
    l () () ∧ Interminable l () ∧ Covered () ∧ ¬ EverlastingAt h () ()) ∧
  (∃ (h : History Unit Unit Unit) (l : Unit → Unit → Prop),
    l () () ∧ Covered () ∧ Interminable l () ∧ LifeToBeing h () l () ∧
    EverlastingAt h () ())
end TruthCore.Causality.TemporalCoverageEternity
