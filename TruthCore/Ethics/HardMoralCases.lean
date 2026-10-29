import TruthCore.Ethics.MoralAccessFibers
import TruthCore.Modal.DeonticFutureBoundary

/-! Analyst controls for #699. These assignments are not representations of
complete historical theories or claims about metaphysically possible worlds.
A false prohibition bit does not mean permission. -/
namespace TruthCore.Ethics.HardMoralCases
open TruthCore.Ethics.MoralAccessFibers
open TruthCore.Modal.DeonticFutureBoundary

/-- The offender's indifference and reason are independent supplied fields.
The prohibition remains the existing fixed-case predicate. -/
structure Case where
  moral : State
  indifferent : Bool
  categoricalReason : Bool

def Reason (c : Case) : Prop := c.categoricalReason = true

def Controls : Prop :=
  (∃ x y : Case, x.moral = y.moral ∧ x.indifferent = true ∧
    y.indifferent = true ∧ Prohibited x.moral ∧ Reason x ∧ ¬ Reason y) ∧
  (∃ x y : State, x.report = y.report ∧ x.basis = y.basis ∧
    Prohibited x ∧ ¬ Prohibited y) ∧
  (∃ (i₁ i₂ available : TruthCore.Modal.Frame Bool) (recognizedGood : Bool → Prop),
    recognizedGood true ∧ recognizedGood false ∧
    (∃ v, i₁.access false v ∧ available.access false v) ∧
    (∃ v, i₂.access false v ∧ available.access false v) ∧
    Can available false (fun v => v = true) ∧
    Can available false (fun v => v = false) ∧
    Ought i₁ false (fun v => v = true) ∧
    Ought i₂ false (fun v => v = false))

end TruthCore.Ethics.HardMoralCases
