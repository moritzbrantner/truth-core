module

public import TruthCore.Logic.FitchKnowability
public import TruthCore.Logic.CommonKnowerScopes

/-! Analyst completion of distributed someone/sometime K. Contents are the exact
world predicates of FitchKnowability.Context, not syntactic sentences. Agent,
time and world domains are arbitrary and may be empty. Knowledge is primitive:
`knows a t p w` means agent a at time t knows content p at world w. Its epistemic
adequacy remains open; no factivity, completeness or omniscience is built in.
Sentence representation and temporal truth require calibration before using
this extensional interpretation for a language with time-sensitive contents. -/
@[expose] public section
namespace TruthCore.Logic.DistributedKnowledge

/-- Some agent at some time knows this SAME content at this SAME world.
The agent and time witnesses can vary with the content and world. -/
def Known {Agent Time W : Type}
    (knows : Agent → Time → (W → Prop) → W → Prop)
    (p : W → Prop) (w : W) : Prop :=
  ∃ a t, knows a t p w

/-- Interpret distributed K in the existing Fitch context; modal accessibility
is supplied independently of knowledge, without any epistemic-frame equation. -/
def context {Agent Time W : Type}
    (knows : Agent → Time → (W → Prop) → W → Prop)
    (modal : TruthCore.Modal.Frame W) (actual : W) : FitchKnowability.Context W :=
  ⟨modal, actual, Known knows⟩

/-- Explicit calibration: witness factivity concerns p at w, not a different
world or a temporal truth predicate. Conjunction extraction keeps the witness.
No exchange of existential witnesses across contents occurs. -/
theorem globalLaws {Agent Time W : Type}
    (knows : Agent → Time → (W → Prop) → W → Prop)
    (modal : TruthCore.Modal.Frame W) (actual : W)
    (factive : ∀ a t p w, knows a t p w → p w)
    (extract : ∀ a t p q w, knows a t (fun v => p v ∧ q v) w →
      knows a t p w ∧ knows a t q w) :
    FitchKnowability.GlobalLaws (context knows modal actual) := by
  constructor
  · rintro p w ⟨a, t, h⟩
    exact factive a t p w h
  · rintro p q w ⟨a, t, h⟩
    obtain ⟨hp, hq⟩ := extract a t p q w h
    exact ⟨⟨a, t, hp⟩, ⟨a, t, hq⟩⟩

/-- Exact actual per-truth scope bridge. The existing common-knower vocabulary
receives an agent's some-time knowledge, with world held at actuality. -/
theorem actualScope {Agent Time W : Type}
    (knows : Agent → Time → (W → Prop) → W → Prop) (actual : W) :
    (∀ p, p actual → Known knows p actual) ↔
      CommonKnowerScopes.EveryTruthKnown (fun p => p actual)
        (fun a p => ∃ t, knows a t p actual) := by
  rfl

/-- Finite control only. Agent and time vary with content, so knowing each
content does not give either one common agent or one common time. -/
theorem changingWitnesses :
    (∀ p : Bool, ∃ a t : Bool, a = p ∧ t = p) ∧
    ¬ (∃ a : Bool, ∀ p : Bool, ∃ t : Bool, a = p ∧ t = p) ∧
    ¬ (∃ t : Bool, ∀ p : Bool, ∃ a : Bool, a = p ∧ t = p) := by
  refine ⟨fun p => ⟨p, p, rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨a, h⟩
    obtain ⟨_, ht, _⟩ := h true
    obtain ⟨_, hf, _⟩ := h false
    exact Bool.noConfusion (ht.symm.trans hf)
  · rintro ⟨t, h⟩
    obtain ⟨_, _, ht⟩ := h true
    obtain ⟨_, _, hf⟩ := h false
    exact Bool.noConfusion (ht.symm.trans hf)

/-- Finite control: different agents know opposite Boolean-world contents;
no agent knows their conjunction. This is a scope counterexample, not a factive
model at all worlds or an intended model of all human knowledge. -/
theorem noConjunctionExchange :
    let k := fun (a : Bool) (_ : Unit) (p : Bool → Prop) (_ : Bool) =>
      p = (fun v => v = a)
    Known k (fun v => v = true) true ∧
    Known k (fun v => v = false) true ∧
    ¬ Known k (fun v => v = true ∧ v = false) true := by
  refine ⟨⟨true, (), rfl⟩, ⟨false, (), rfl⟩, ?_⟩
  rintro ⟨a, t, h⟩
  have hh : a = true ∧ a = false := by
    have he := congrFun h a
    exact he.mpr rfl
  exact Bool.noConfusion (hh.1.symm.trans hh.2)

/-- Finite control: possible knowledge at another world does not supply actual
knowledge or actual truth. Modal R is universal here; K is evaluated locally. -/
theorem possibleNotActual :
    let k := fun (_ : Unit) (_ : Unit) (p : Bool → Prop) w => p w
    let c := context k ⟨fun _ _ => True⟩ false
    FitchKnowability.PossibleKnown c (fun w => w = true) false ∧
    ¬ Known k (fun w => w = true) false := by
  refine ⟨⟨true, trivial, (), (), rfl⟩, ?_⟩
  rintro ⟨a, t, h⟩
  exact Bool.noConfusion h

end TruthCore.Logic.DistributedKnowledge
