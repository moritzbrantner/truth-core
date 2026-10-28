import TruthCore.Modal.Kripke

/-! Analyst stipulations prompted by Carneades.org, “The Paradox of Kant's
Law (Ought Implies Can)”, 00:42–05:26 (qjNs4t4GQ2A). Provisional captions
are reading leads, not a pinned source claim or authenticated Kant reading.
States encode complete continuations; the supplied future relation means
reachable through the agent's choices, not mere logical possibility. No agency
or temporal property is inferred from the name of that relation. -/
namespace TruthCore.Modal.DeonticFutureBoundary

/-- Ideal-successor semantics for obligation, not a premise that actual duties
have this semantics. No duty follows merely by selecting a frame. -/
def Ought (ideal : Frame W) (w : W) (p : W → Prop) : Prop :=
  ∀ v, ideal.access w v → p v

/-- Fulfillment in at least one supplied accessible continuation. Depending on
the explicit frame this can mean feasible future or broad logical possibility;
these readings are never identified. It is neither permission nor actual doing. -/
def Can (available : Frame W) (w : W) (p : W → Prop) : Prop :=
  ∃ v, available.access w v ∧ p v

/-- Universal ought-implies-can holds exactly when ideal and available successor
sets overlap. Necessity uses the ideal-successor set itself as a valuation;
no classical choice, finiteness or seriality assumption is needed. -/
theorem compatibility (ideal available : Frame W) (w : W) :
    (∀ p, Ought ideal w p → Can available w p) ↔
      ∃ v, ideal.access w v ∧ available.access w v := by
  constructor
  · intro h
    obtain ⟨v, hav, hid⟩ := h (ideal.access w) (fun _ hv => hv)
    exact ⟨v, hid, hav⟩
  · rintro ⟨v, hid, hav⟩ p hp
    exact ⟨v, hav, hp v hid⟩

/-- Bool false is nonfulfillment; true is fulfillment. The current point is
false. These frames are finite interpretations, not empirical possibilities. -/
def goal (v : Bool) : Prop := v = true
def ideal : Frame Bool := ⟨fun _ v => v = true⟩
def broad : Frame Bool := ⟨fun _ _ => True⟩
def blocked : Frame Bool := ⟨fun _ v => v = false⟩

/-- One exact correspondence and two closed boundary controls: a serial ideal
frame with broad possible fulfillment but no feasible fulfillment; and a
compatible alternative-future frame with no fulfillment on the selected actual
continuation. Present fulfillment also fails. No moral premise is discharged. -/
def Certificate : Prop :=
  (∀ (W : Type) (i a : Frame W) w,
    (∀ p, Ought i w p → Can a w p) ↔ ∃ v, i.access w v ∧ a.access w v) ∧
  (Serial ideal ∧ Ought ideal false goal ∧ Can broad false goal ∧
    ¬ Can blocked false goal) ∧
  ((∀ p, Ought ideal false p → Can broad false p) ∧
    ¬ goal false ∧ ¬ Can blocked false goal)

end TruthCore.Modal.DeonticFutureBoundary
