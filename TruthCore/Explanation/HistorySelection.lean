import TruthCore.Modal.HistoryContrastive
import TruthCore.Causality.UniqueFeedback
import TruthCore.Causality.EssentialPower
import TruthCore.Causality.SourceWitness

/-! #736: informational selection, not a definition of metaphysical adequacy.
An arbitrary reason-vector is allowed, including infinitely many local facts.
`EvidenceOnly` tests extensional dependence on that ENTIRE vector; no finitary
proof, causal origin, external source or well-foundedness is required. -/
namespace TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

/-- Two worlds agree on every admitted item of information. This compares
truth, not the numerical identity or causal origin of reason tokens. -/
def SameEvidence (truth : W → R → Prop) (basis : R → Prop) (v w : W) : Prop :=
  ∀ r, basis r → (truth v r ↔ truth w r)

/-- A proposed reason adds no distinctions beyond the whole supplied vector.
This includes arbitrary infinitary functions of that vector. It excludes a
fresh actuality marker unless its truth is already determined by the vector.
It is informational dependence, not a causal or grounding relation. -/
def EvidenceOnly (truth : W → R → Prop) (basis : R → Prop) (p : W → Prop) : Prop :=
  ∀ v w, SameEvidence truth basis v w → (p v ↔ p w)

/-- Within the selected accessibility component, the entire reason-vector
fixes the complete supplied presence extension. No metaphysical adequacy or
ontological production is contained in this mathematical condition. -/
def Determines (h : History W B T) (truth : W → R → Prop)
    (basis : R → Prop) (a : W) : Prop :=
  ∀ v, h.ontic.frame.access a v → SameEvidence truth basis v a → SameHistory h v a

/-- A single candidate proposition passes the existing entailing history test.
Unit tags a proposition; no extra ontic object or aggregate being is added. -/
def Selects (h : History W B T) (p : W → Prop) (a : W) : Prop :=
  Discriminates h (fun w (_ : Unit) => p w) a ()

/-- All two-gate constraints are imposed at every integer time. This is a
beginningless constraint system, not an efficient-cause interpretation of gates.
The existing unique-feedback result must supply its solution and uniqueness. -/
def GlobalLaw (signal : Int → Bool × Bool) : Prop :=
  ∀ t, TruthCore.Causality.UniqueFeedback.Consistent (signal t)

def fixedSignal (_ : Int) : Bool × Bool := (true, false)

/-- Beginningless copying dependency; the extra gate law is an independent
structural constraint. Edges are NOT certified efficient causes or grounds. -/
def predecessor : TruthCore.Logic.Regress.Graph Int := ⟨fun y x => y = x + 1⟩

/-- The SAME presence histories as `chains`, with an explicit source per
world replacing the predecessor graph. Time/presence/reasons/accessibility do
not change. A source need not thereby explain its own actuality. -/
def rooted : History Bool (Bool × Nat) Nat :=
  { chains with ontic := { chains.ontic with
      Causes := fun w y x => y = (w, 0) ∧ x.1 = w ∧ x.2 ≠ 0 } }

/-- General characterization, infinite-bundle omission, beginningless unique
solution, and a common-explanandum source comparison. No adequate-explanation
predicate is defined: applying this entailing standard to ultimate explanation
is the explicitly OPEN philosophical bridge in the linked note. -/
def Certificate : Prop :=
  (∀ (W B T R : Type) (h : History W B T) (truth : W → R → Prop)
      (basis : R → Prop) (a : W),
    Determines h truth basis a ↔
      ∃ p, EvidenceOnly truth basis p ∧ Selects h p a) ∧
  (∀ (W B T R : Type) (h : History W B T) (truth : W → R → Prop)
      (basis : R → Prop) (a v : W),
    h.ontic.frame.access a v → ¬ SameHistory h v a →
    SameEvidence truth basis v a →
    ¬ ∃ p, EvidenceOnly truth basis p ∧ Selects h p a) ∧
  TruthCore.Causality.EssentialPowerUnderdetermined ∧
  (GlobalLaw fixedSignal ∧ ∀ signal, GlobalLaw signal → signal = fixedSignal) ∧
  (∀ t : Int, ∃ s : Int, s < t) ∧
  (∀ t, predecessor.edge (t + 1) t ∧ ¬ predecessor.Source t ∧
    fixedSignal (t + 1) = fixedSignal t) ∧
  (¬ Determines chains (reasons false).reasonPresent (fun _ => True) false ∧
    ¬ Determines rooted (reasons false).reasonPresent (fun _ => True) false) ∧
  (∀ w, ∃ s, rooted.ontic.ExistsAt w s ∧
    (∀ y, ¬ rooted.ontic.Causes w y s) ∧
    ∀ x, rooted.ontic.ExistsAt w x → x ≠ s → rooted.ontic.Causes w s x) ∧
  (Determines chains (reasons true).reasonPresent (fun _ => True) false ∧
    Determines rooted (reasons true).reasonPresent (fun _ => True) false) ∧
  TruthCore.Causality.SourceWitness.ConfluentOverlapControl

end TruthCore.Explanation.HistorySelection

namespace TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive

/-- Same populated alternatives, but the selected component contains only
itself. This is an accessibility omission, not proof that a rival is impossible. -/
def isolated : History Bool (Bool × Nat) Nat :=
  { chains with ontic := { chains.ontic with frame := ⟨fun v w => v = w⟩ } }

/-- All worlds have the same populated history; no distinguishing task remains. -/
def repeated : History Bool Unit Nat where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun _ _ => True
    Causes := fun _ _ _ => False
  }
  IsAt := fun _ _ _ => True
  now := 0

/-- Positive weights illustrate comparative favor without exclusion. These
are formal weights, not an empirically justified chance law or adequacy proof. -/
def weight (w : Bool) : Nat := if w then 1 else 2

/-- Omit accessible rivalry, distinctness, evidence-only dependence, or actual
truth in turn. The last conjunct retains both positive weights, illustrating
that comparative favor need not be an entailing selection standard. -/
def OmissionControls : Prop :=
  (Determines isolated (reasons false).reasonPresent (fun _ => True) false ∧
    ¬ SameHistory isolated true false) ∧
  Determines repeated (fun _ (_ : Unit) => True) (fun _ => True) false ∧
  (Selects chains (fun w => w = false) false ∧
    ¬ EvidenceOnly (reasons false).reasonPresent (fun _ => True) (fun w => w = false)) ∧
  (∀ v, chains.ontic.frame.access false v →
    False → SameHistory chains v false) ∧
  ¬ Selects chains (fun _ => False) false ∧
  (0 < weight false ∧ 0 < weight true ∧ weight true < weight false)
end TruthCore.Explanation.HistorySelection
