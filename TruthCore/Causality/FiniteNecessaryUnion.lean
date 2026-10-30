import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Models.NecessarilyUnderived
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite necessary-support unions

Source-free conditional graph analysis for #604. Edges retain the existing
existence-support interpretation; none of these backgrounds is established.
A cycle means a nonempty `Relation.TransGen` loop, never reflexive reachability.
Sources and cycles may coexist in different parts of the same union.
-/
namespace TruthCore.Causality.FiniteNecessaryUnion

open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

variable {World Being : Type}

abbrev Carrier (m : Ontic World Being) (w₀ : World) :=
  {x : Being // NecessaryAt m w₀ x}

def Edge (m : Ontic World Being) (s : World → Being → Being → Prop) (w₀ : World)
    (a b : Carrier m w₀) : Prop := UnionNecessarySupport m s w₀ a.val b.val

def FinitePopulation (m : Ontic World Being) (w₀ : World) : Prop :=
  Finite (Carrier m w₀) ∧ Nonempty (Carrier m w₀)

def HasSource (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) : Prop := ∃ b : Carrier m w₀, ∀ a, ¬ Edge m s w₀ a b

def HasCycle (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) : Prop := ∃ b : Carrier m w₀, Relation.TransGen (Edge m s w₀) b b

def SourceOrCycle (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) : Prop := HasSource m s w₀ ∨ HasCycle m s w₀

/-- Finite nonempty carriers without a source have a nonempty directed loop.
The conclusion is inclusive: a separate source does not eliminate a cycle. -/
theorem source_or_cycle (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) (h : FinitePopulation m w₀) : SourceOrCycle m s w₀ := by
  classical
  let : Finite (Carrier m w₀) := h.1
  by_cases hs : HasSource m s w₀
  · exact Or.inl hs
  · right
    by_contra hc
    have hirr : ∀ x, ¬ Relation.TransGen (Edge m s w₀) x x := by
      intro x hx
      exact hc ⟨x, hx⟩
    let : Std.Irrefl (Relation.TransGen (Edge m s w₀)) := ⟨hirr⟩
    have wf := Finite.wellFounded_of_trans_of_irrefl
      (Relation.TransGen (Edge m s w₀))
    obtain ⟨initial⟩ := h.2
    have impossible : ∀ x : Carrier m w₀, False := by
      intro x
      induction wf.apply x with
      | intro x _ ih =>
        apply hs
        refine ⟨x, ?_⟩
        intro a ha
        exact ih a (Relation.TransGen.single ha)
    exact impossible initial

/-- Exact no-source consequence; inhabitedness is essential. -/
theorem cycle_of_no_source (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (h : FinitePopulation m w₀) (hs : ¬ HasSource m s w₀) : HasCycle m s w₀ :=
  (source_or_cycle m s w₀ h).resolve_left hs

/-- Union acyclicity suffices for a source on the finite nonempty carrier.
The independent source-plus-cycle control refutes necessity of acyclicity. -/
theorem source_of_no_cycle (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (h : FinitePopulation m w₀) (hc : ¬ HasCycle m s w₀) : HasSource m s w₀ :=
  (source_or_cycle m s w₀ h).resolve_right hc

/-- The source itself is the common underived necessary individual. Actual
reflexivity supplies its actual presence; no-contingent-ground ensures that
any existing incoming supporter belongs to the restricted carrier. -/
theorem underived_of_source (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (hs : HasSource m s w₀) (hr : ActualReflexive m w₀)
    (hn : NoContingentGroundOfNecessary m s w₀) : NecessarilyUnderived m s w₀ := by
  obtain ⟨b, hb⟩ := hs
  refine ⟨b.val, b.property w₀ hr, b.property, ?_⟩
  intro w a ha he
  have han := hn w a b.val ha b.property he
  exact hb ⟨a, han⟩ ⟨han, b.property, w, ha, he⟩

/-- Local acyclicity uses the same necessary-carrier restriction as the union. -/
def LocallyAcyclic (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) : Prop := ∀ w (b : Carrier m w₀),
  ¬ Relation.TransGen (fun a b : Carrier m w₀ => PresentEsseSupport m s w a.val b.val) b b

/-- No union loop can have every edge witnessed in one selected world. This
concerns an entire nonempty path, not merely two opposite direct edges. -/
def NoSingleWorldCycle (m : Ontic World Being) (s : World → Being → Being → Prop)
    (w₀ : World) : Prop := ∀ w (b : Carrier m w₀),
  ¬ Relation.TransGen (fun a b : Carrier m w₀ =>
    Edge m s w₀ a b ∧ PresentEsseSupport m s w a.val b.val) b b

theorem no_single_world_cycle (m : Ontic World Being)
    (s : World → Being → Being → Prop) (w₀ : World)
    (h : LocallyAcyclic m s w₀) : NoSingleWorldCycle m s w₀ := by
  intro w b hp
  exact h w b (Relation.TransGen.mono (fun _ _ he => he.2) b b hp)

/-- Independent source plus a two-cycle: acyclicity is sufficient, not necessary,
for source existence. All three individuals exist in the one admitted world. -/
def coexistSupport (_ : Unit) (a b : Fin 3) : Prop :=
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

def coexist : Ontic Unit (Fin 3) where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := coexistSupport

def SourceCycleControl : Prop :=
  HasSource coexist coexistSupport () ∧ HasCycle coexist coexistSupport ()

theorem source_cycle_control : SourceCycleControl := by
  have nec : ∀ x : Fin 3, NecessaryAt coexist () x := by intro _ _ _; trivial
  constructor
  · refine ⟨⟨0, nec 0⟩, ?_⟩
    rintro a ⟨_, _, w, _, he⟩
    rcases he with ⟨_, he⟩ | ⟨_, he⟩ <;> exact (by decide : ¬ ((0 : Fin 3) = _)) he
  · refine ⟨⟨1, nec 1⟩, ?_⟩
    apply Relation.TransGen.trans (b := ⟨2, nec 2⟩)
    · exact Relation.TransGen.single ⟨nec 1, nec 2, (), trivial, Or.inl ⟨rfl, rfl⟩⟩
    · exact Relation.TransGen.single ⟨nec 2, nec 1, (), trivial, Or.inr ⟨rfl, rfl⟩⟩

/-- Closed conditional bridge, with each metaphysical background explicit. -/
def SourceUnderivedBridge : Prop := ∀ (W B : Type) (m : Ontic W B)
    (s : W → B → B → Prop) (w₀ : W),
    HasSource m s w₀ → ActualReflexive m w₀ →
    NoContingentGroundOfNecessary m s w₀ → NecessarilyUnderived m s w₀

theorem source_underived_bridge : SourceUnderivedBridge := by
  intro W B m s w₀ hs hr hn
  exact underived_of_source m s w₀ hs hr hn

/-- The unchanged rotating model has locally acyclic restricted support but
no common source; the finite classification therefore supplies its union loop. -/
def RotatingControl : Prop :=
  LocallyAcyclic TruthCore.Models.NecessarilyUnderived.rotating
    TruthCore.Models.NecessarilyUnderived.rotatingSupport false ∧
  ¬ HasSource TruthCore.Models.NecessarilyUnderived.rotating
    TruthCore.Models.NecessarilyUnderived.rotatingSupport false ∧
  HasCycle TruthCore.Models.NecessarilyUnderived.rotating
    TruthCore.Models.NecessarilyUnderived.rotatingSupport false

theorem rotating_control : RotatingControl := by
  let m := TruthCore.Models.NecessarilyUnderived.rotating
  let s := TruthCore.Models.NecessarilyUnderived.rotatingSupport
  have hn : ¬ HasSource m s false := by
    intro hs
    exact TruthCore.Models.NecessarilyUnderived.rotatingNoUnderived
      (underived_of_source m s false hs
        TruthCore.Models.NecessarilyUnderived.rotatingReflexive
        TruthCore.Models.NecessarilyUnderived.rotatingNoContingentGround)
  refine ⟨?_, hn, ?_⟩
  · intro w b hp
    have wf := TruthCore.Models.NecessarilyUnderived.rotatingWorldWellFounded w
    have loop := Relation.TransGen.lift (fun x : Carrier m false => x.val)
      (fun _ _ h => h) b b hp
    exact @WellFounded.asymmetric _ _ wf.transGen b.val b.val loop loop
  · have hp : FinitePopulation m false := by
      constructor
      · exact Finite.of_injective (fun x : Carrier m false => x.val) Subtype.val_injective
      · exact ⟨⟨false, by intro _ _; trivial⟩⟩
    exact (source_or_cycle m s false hp).resolve_left hn

/-- Reuse the benign variable-edge model: it has a common source and no loop,
even though some necessary support edges are novel outside the actual world. -/
def VaryingControl : Prop :=
  HasSource TruthCore.Models.NecessarilyUnderived.varying
    TruthCore.Models.NecessarilyUnderived.varyingSupport false ∧
  ¬ HasCycle TruthCore.Models.NecessarilyUnderived.varying
    TruthCore.Models.NecessarilyUnderived.varyingSupport false ∧
  ¬ NoNovelNecessarySupport TruthCore.Models.NecessarilyUnderived.varying
    TruthCore.Models.NecessarilyUnderived.varyingSupport false

theorem varying_control : VaryingControl := by
  obtain ⟨b, _, hb, hu⟩ := TruthCore.Models.NecessarilyUnderived.varyingUnderived
  refine ⟨⟨⟨b, hb⟩, ?_⟩, ?_,
    TruthCore.Models.NecessarilyUnderived.varyingNoNovelSupport⟩
  · rintro a ⟨_, _, w, ha, he⟩
    exact hu w a.val ha he
  · rintro ⟨b, hp⟩
    have loop := Relation.TransGen.lift (fun x => x.val)
      (fun _ _ h => h) b b hp
    exact @WellFounded.asymmetric _ _
      TruthCore.Models.NecessarilyUnderived.varyingUnionWellFounded.transGen
      b.val b.val loop loop

/-- Three joint controls: source with cycle, locally acyclic without source,
and a source without cycle despite novel world-varying support. -/
def ModelControls : Prop := SourceCycleControl ∧ RotatingControl ∧ VaryingControl

theorem model_controls : ModelControls :=
  ⟨source_cycle_control, rotating_control, varying_control⟩

end TruthCore.Causality.FiniteNecessaryUnion
