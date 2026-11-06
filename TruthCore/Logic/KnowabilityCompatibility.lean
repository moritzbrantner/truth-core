module

public import TruthCore.Logic.FitchKnowability

/-!
Analyst formulations for #1059; attribution deferred. Modal accessibility R
and the fixed agent's epistemic alternatives E remain distinct. E ⊆ R means
only that each epistemic alternative is modally admitted, not that the two
relations coincide, commute, or describe changes over time. Applicability to
actual knowledge and metaphysical possibility remains OPEN.
-/

@[expose] public section

namespace TruthCore.Logic.KnowabilityCompatibility
open TruthCore.Modal TruthCore.Logic.FitchKnowability

/-- Construct the existing Context with the existing relational knowledge
operator. This adapter introduces neither another K nor an additional law. -/
def relationalContext {W : Type} (E R : Frame W) (actual : W) : Context W :=
  ⟨R, actual, JustificationIntrospection.Knows E⟩

/-- Every epistemic alternative is modally accessible at the same world. This
is an explicit bridge, not a consequence of either relation's name. -/
def Included {W : Type} (E R : Frame W) : Prop :=
  ∀ u v, E.access u v → R.access u v

/-- Forward knowability at every world, without the reverse implication. -/
def GlobalForward {W : Type} (c : Context W) (C : (W → Prop) → Prop) : Prop :=
  ∀ p, C p → ∀ w, p w → PossibleKnown c p w

/-- Only the supplied admissible contents are conditionally known. This is
not knowledge of every predicate unless C is separately made unrestricted. -/
def AdmittedKnown {W : Type} (c : Context W) (C : (W → Prop) → Prop) : Prop :=
  ∀ p, C p → ∀ w, p w → c.knows p w

local instance : NeZero 4 := ⟨Nat.noConfusion⟩

/-- All four existing worlds are modally possible. Epistemic knowledge and
admissible contents are exactly those of the earlier survivor. -/
def universalModal : Frame (Fin 4) where
  access _ _ := True

def forwardContext : Context (Fin 4) :=
  relationalContext survivorEpistemic universalModal 0

/-- Union of the SAME old epistemic and modal relations: the reflexive,
symmetric line 2–0–1–3. No transitive closure is imposed. -/
def lineModal : Frame (Fin 4) where
  access u v := survivorEpistemic.access u v ∨ survivorModal.access u v

def lineContext : Context (Fin 4) :=
  relationalContext survivorEpistemic lineModal 0

/-- Forward-only global restricted knowability coexists with actual ignorance,
E ⊆ R and both S5 frames. The stronger reverse schema actually fails. -/
def ForwardSurvivor : Prop :=
  let E := survivorEpistemic
  let c := forwardContext
  let C := AtomInvariant survivorAtom
  Reflexive E ∧ Symmetric E ∧ Transitive E ∧
  Reflexive c.modal ∧ Symmetric c.modal ∧ Transitive c.modal ∧ Euclidean c.modal ∧
  Included E c.modal ∧ GlobalLaws c ∧ BooleanClosed C ∧ C survivorAtom ∧
  GlobalForward c C ∧ Moore c survivorAtom c.actual ∧
  ¬ GlobalRestrictedEquivalence c C ∧ ¬ MooreAdmissible c C survivorAtom

/-- Removing Euclideanness permits even the biconditional with compatibility
and ignorance. The modal frame is reflexive/symmetric, not Euclidean. -/
def LineSurvivor : Prop :=
  let E := survivorEpistemic
  let c := lineContext
  let C := AtomInvariant survivorAtom
  Reflexive E ∧ Symmetric E ∧ Transitive E ∧
  Reflexive c.modal ∧ Symmetric c.modal ∧ ¬ Euclidean c.modal ∧
  Included E c.modal ∧ GlobalLaws c ∧ BooleanClosed C ∧ C survivorAtom ∧
  GlobalRestrictedEquivalence c C ∧ Moore c survivorAtom c.actual ∧
  ¬ MooreAdmissible c C survivorAtom

end TruthCore.Logic.KnowabilityCompatibility
