import TruthCore.Modal.ResearchFixture
import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

/-!
Stipulated quantifier diagnostics for #435, not attributed source readings.
The ambient individual type is a fixed possibilist roster with literal Lean
identity across worlds; `ex` selects its world-dependent actualist extension.
A world is an element of the supplied type, not an existentially asserted
metaphysical possibility. The actual world is an explicit argument.
Concreteness is an independent, theory-relative predicate: no causal,
spatiotemporal or independence criterion is assumed or defended here.
-/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

universe u v
variable {W : Type u} {I : Type v}

/-- Existing concrete individuals: existence and the supplied concreteness
criterion must both hold. The criterion alone does not confer existence. -/
def ConcreteAt (ex concrete : ExistsAt W I) : ExistsAt W I :=
  fun x w => ex x w ∧ concrete x w

/-- One fixed bearer has the supplied presence property in every successor.
The outer quantifier is possibilist; no actuality at `w` is implicit. -/
def DeRe (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  ∃ x, Box F (present x) w

/-- Every successor has a bearer, which may vary with the successor. -/
def DeDicto (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  Box F (fun v => ∃ x, present x v) w

/-- Every member of the fixed roster is absent at some accessible world. -/
def IndividualContingency (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  ∀ x, Dia F (fun v => ¬ present x v) w

/-- Some accessible world has an empty presence extension; the world itself
still exists as an element of W. -/
def JointAbsence (F : Frame W) (present : ExistsAt W I) (w : W) : Prop :=
  Dia F (fun v => ¬ ∃ x, present x v) w

/-- A fixed necessary bearer supplies a bearer at each successor. -/
theorem deRe_to_deDicto (F : Frame W) (present : ExistsAt W I) (w : W)
    (h : DeRe F present w) : DeDicto F present w := by
  obtain ⟨x, hx⟩ := h
  exact fun v hv => ⟨x, hx v hv⟩

/-- The actualist outer-quantifier variant retains the same implication;
actual existence is explicit rather than inferred from box without T. -/
theorem actual_deRe_to_deDicto (F : Frame W) (ex : ExistsAt W I) (w : W)
    (h : ∃ x, ex x w ∧ Box F (ex x) w) : DeDicto F ex w := by
  obtain ⟨x, _, hx⟩ := h
  exact deRe_to_deDicto F ex w ⟨x, hx⟩

/-- Existing necessarily does not imply concrete necessarily unless a bridge
is supplied. Only successor-relative existence-to-concreteness is needed. -/
theorem deRe_exists_to_concrete (F : Frame W) (ex concrete : ExistsAt W I) (w : W)
    (bridge : ∀ v, F.access w v → ∀ x, ex x v → concrete x v)
    (h : DeRe F ex w) : DeDicto F (ConcreteAt ex concrete) w := by
  obtain ⟨x, hx⟩ := h
  exact fun v hv => ⟨x, hx v hv, bridge v hv x (hx v hv)⟩

/-- A jointly empty extension makes each fixed individual absent there. -/
theorem joint_to_individual (F : Frame W) (present : ExistsAt W I) (w : W)
    (h : JointAbsence F present w) : IndividualContingency F present w := by
  obtain ⟨v, hv, hn⟩ := h
  exact fun x => ⟨v, hv, fun hx => hn ⟨x, hx⟩⟩

/-- Reuse the Third Way's existing collective-possibility proposition, with
Kripke Dia substituted for its primitive Possible. The iff uses no temporal
plenitude and does not identify worlds with times metaphysically. -/
theorem collective_iff (F : Frame W) (ex : ExistsAt W I) (w : W) :
    TruthCore.Latin.Aquinas.SummaTheologiae.AllCanNotBeThenNothingPossibleReading
      (fun P => Dia F P w) ex ↔
    (IndividualContingency F ex w → JointAbsence F ex w) := by
  constructor
  · intro h hc
    obtain ⟨v, hv, hn⟩ := h hc
    exact ⟨v, hv, fun ⟨x, hx⟩ => hn x hx⟩
  · intro h hc
    obtain ⟨v, hv, hn⟩ := h hc
    exact ⟨v, hv, fun x hx => hn ⟨x, hx⟩⟩

/-- All domain assumptions are quantified; no inhabitedness is needed for
these conditional laws. Instantiating `w` already witnesses an inhabited W. -/
def Laws : Prop :=
  (∀ (W I : Type) (F : Frame W) (ex : ExistsAt W I) w,
    DeRe F ex w → DeDicto F ex w) ∧
  (∀ (W I : Type) (F : Frame W) (ex : ExistsAt W I) w,
    (∃ x, ex x w ∧ Box F (ex x) w) → DeDicto F ex w) ∧
  (∀ (W I : Type) (F : Frame W) (ex concrete : ExistsAt W I) w,
    (∀ v, F.access w v → ∀ x, ex x v → concrete x v) →
    DeRe F ex w → DeDicto F (ConcreteAt ex concrete) w) ∧
  (∀ (W I : Type) (F : Frame W) (ex : ExistsAt W I) w,
    JointAbsence F ex w → IndividualContingency F ex w) ∧
  (∀ (W I : Type) (F : Frame W) (ex : ExistsAt W I) w,
    TruthCore.Latin.Aquinas.SummaTheologiae.AllCanNotBeThenNothingPossibleReading
      (fun P => Dia F P w) ex ↔
    (IndividualContingency F ex w → JointAbsence F ex w))

/-- Two worlds and two rigid individuals; every world accesses both worlds. -/
def alternatingFrame : Frame Bool := ⟨fun _ _ => True⟩

/-- Individual false exists only at world false; true only at world true. -/
def alternatingExists : ExistsAt Bool Bool := fun x w => x = w

/-- All roster members satisfy this stipulated criterion whenever present. -/
def alternatingConcrete : ExistsAt Bool Bool := fun _ _ => True

/-- Formal countermodel at explicit actual world false. Reflexivity, a distinct
accessible world and actual concrete existence rule out empty-world/vacuity
shortcuts. Both invalid quantifier directions fail in this very same model. -/
def AlternatingCountermodel : Prop :=
  Reflexive alternatingFrame ∧
  alternatingFrame.access false true ∧ true ≠ false ∧
  (∃ x, ConcreteAt alternatingExists alternatingConcrete x false) ∧
  IndividualContingency alternatingFrame alternatingExists false ∧
  DeDicto alternatingFrame (ConcreteAt alternatingExists alternatingConcrete) false ∧
  ¬ DeRe alternatingFrame alternatingExists false ∧
  ¬ JointAbsence alternatingFrame (ConcreteAt alternatingExists alternatingConcrete) false ∧
  ¬ TruthCore.Latin.Aquinas.SummaTheologiae.AllCanNotBeThenNothingPossibleReading
      (fun P => Dia alternatingFrame P false) alternatingExists

/-- Nonempty worlds and existing individuals can coexist with an empty concrete
extension under a supplied criterion. This distinguishes the two predicates;
it does not defend a theory admitting this criterion. -/
def ConcreteBridgeCountermodel : Prop :=
  DeRe alternatingFrame (fun (_ : Bool) (_ : Bool) => True) false ∧
  JointAbsence alternatingFrame
    (ConcreteAt (fun (_ : Bool) (_ : Bool) => True) (fun _ _ => False)) false ∧
  ¬ DeDicto alternatingFrame
    (ConcreteAt (fun (_ : Bool) (_ : Bool) => True) (fun _ _ => False)) false

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
