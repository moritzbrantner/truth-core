module

public import TruthCore.Modal.Kripke

/-! Analyst semantics for #1049, motivated by SEP Modal Logic §§10/16;
historical attribution is deferred. The first coordinate fixes the designated
actual world/context; the second is the evaluation world. Box changes ONLY the
second coordinate. A designation policy admits choices of the first coordinate
on one fixed frame/valuation/ontology; it is not a claim of real actuality.

These predicates quantify over denotations, not a new object language or proof
calculus. In particular, unrestricted two-index quantification can exceed the
expressive power of a chosen language. Neither local assumptions nor semantic
validity are identified with theoremhood. No existence-domain, frame law,
inhabitedness, causal relation or metaphysical application is built in. -/

@[expose] public section

namespace TruthCore.Modal.DesignatedValidity

variable {W : Type}

/-- True at its own evaluation world for every admitted actual-world choice. -/
def DiagonalValid (D : W → Prop) (F : W → W → Prop) : Prop :=
  ∀ a, D a → F a a

/-- Necessary at every admitted actuality, retaining that SAME actuality index. -/
def NecessitatedValid (frame : Frame W) (D : W → Prop) (F : W → W → Prop) : Prop :=
  ∀ a, D a → ∀ v, frame.access a v → F a v

/-- Each accessible successor of an admissible designation is also admissible. -/
def SuccessorClosed (frame : Frame W) (D : W → Prop) : Prop :=
  ∀ a, D a → ∀ v, frame.access a v → D v

/-- Rule admissibility for every context-independent world predicate P. -/
def IndependentRule (frame : Frame W) (D : W → Prop) : Prop :=
  ∀ P : W → Prop,
    DiagonalValid D (fun _ e => P e) → NecessitatedValid frame D (fun _ e => P e)

/-- The edge-local ONE-WAY content bridge needed by the sufficient theorem:
diagonal truth after redesignating v gives truth there with original context a.
This is not assumed necessary for an individual F, whose premise may fail. -/
def ContentTransport (frame : Frame W) (D : W → Prop) (F : W → W → Prop) : Prop :=
  ∀ a, D a → ∀ v, frame.access a v → F v v → F a v

/-- Rule admissibility over ALL two-index denotations, beyond any fixed syntax. -/
def UnrestrictedRule (frame : Frame W) (D : W → Prop) : Prop :=
  ∀ F : W → W → Prop, DiagonalValid D F → NecessitatedValid frame D F

/-- Admitted worlds have no accessible alternative distinct from themselves.
Self-access is not required: empty successor sets also satisfy this policy. -/
def IdentitySuccessors (frame : Frame W) (D : W → Prop) : Prop :=
  ∀ a, D a → ∀ v, frame.access a v → v = a

/-- Explicit actuality-agreement schema: P holds at the evaluation world iff
it holds at the fixed designated actuality. Its diagonal is always true. -/
def Agreement (P : W → Prop) (a e : W) : Prop := P e ↔ P a

/-- Restrict the candidate theorem rule to the explicit Agreement schema. -/
def AgreementRule (frame : Frame W) (D : W → Prop) : Prop :=
  ∀ P : W → Prop, DiagonalValid D (Agreement P) →
    NecessitatedValid frame D (Agreement P)

end TruthCore.Modal.DesignatedValidity
