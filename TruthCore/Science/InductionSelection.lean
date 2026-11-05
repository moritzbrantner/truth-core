module

public import Mathlib.Logic.Equiv.Defs
public import TruthCore.Science.PredicateRecoding
public import TruthCore.Modern.Hume.Induction

/-! Working argument for #1036; historical attribution is deferred.
Evidence neutrality concerns a supplied recoding, not all physically meaningful
transformations. Set-valued responses represent admitted hypotheses, not degrees
of belief or permission to act. Empty output represents abstention. -/

@[expose] public section
namespace TruthCore.Science.InductionSelection

/-- Two invertible changes of representation, on evidence and hypotheses.
Mathlib equivalences record invertibility; no physical symmetry is asserted. -/
structure Recoding (E H : Type) where
  evidence : Equiv.Perm E
  hypothesis : Equiv.Perm H

/-- Covariance of a response under the supplied representation change. -/
def Neutral {E H : Type} (r : Recoding E H) (answer : E → H → Prop) : Prop :=
  ∀ e h, answer (r.evidence e) (r.hypothesis h) ↔ answer e h

/-- Unique selection at e: precisely one hypothesis is admitted, rather than
merely a nonempty response or a preferred physical coordinate name. -/
def SingletonAt {E H : Type} (answer : E → H → Prop) (e : E) (h : H) : Prop :=
  ∀ k, answer e k ↔ k = h

/-- A deterministic total selector, stricter than a set-valued response. -/
def Equivariant {E H : Type} (r : Recoding E H) (select : E → H) : Prop :=
  ∀ e, select (r.evidence e) = r.hypothesis (select e)

/-- Fixed evidence forces closure of the selected set under recoding. In
particular, a moved hypothesis cannot be the unique admitted hypothesis. -/
def SymmetryConstraint : Prop :=
  ∀ (E H : Type) (r : Recoding E H) (answer : E → H → Prop) (e : E),
    Neutral r answer → r.evidence e = e →
    (∀ h, answer e (r.hypothesis h) ↔ answer e h) ∧
    (∀ h, SingletonAt answer e h → r.hypothesis h = h)

/-- The incompatible bundle: fixed evidence, equivariance and a moved output.
It does not assert that any of these assumptions applies to actual science. -/
def NoUniqueSelector : Prop :=
  ∀ (E H : Type) (r : Recoding E H) (select : E → H) (e : E),
    r.evidence e = e → Equivariant r select →
    r.hypothesis (select e) ≠ select e → False

/-- A nontrivial involution on the two competing predictions. -/
def flip : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

/-- Symmetric evidence: one evidence state, two exchanged hypotheses. -/
def symmetric : Recoding Unit Bool := ⟨Equiv.refl Unit, flip⟩

/-- Asymmetric evidence carries the discriminating bit itself. The equivariant
identity selector succeeds because neither evidence state is fixed. This does
not say that finite pre-divergence observations contain that bit. -/
def asymmetric : Recoding Bool Bool := ⟨flip, flip⟩

/-- A privileged-basis choice: consistent and unique, but not neutral under the
hypothesis swap. Its epistemic/practical warrant is a separate open question. -/
def privileged (_ : Unit) : Bool := true

def both (_ : Unit) (_ : Bool) : Prop := True
def abstain (_ : Unit) (_ : Bool) : Prop := False

/-- Omission controls retain the same recoding semantics. Neither all-neutral
set-valued responses nor a basis-sensitive decision is contradictory. -/
def Alternatives : Prop :=
  Equivariant asymmetric (fun b => b) ∧
  (∀ b, asymmetric.evidence b ≠ b) ∧
  SingletonAt (fun e h => h = privileged e) () true ∧
  ¬ Equivariant symmetric privileged ∧
  Neutral symmetric both ∧ Neutral symmetric abstain ∧
  (∀ answer : Unit → Bool → Prop, Neutral symmetric answer →
    ((∀ h, answer () h) ∨ (∀ h, ¬ answer () h)))

/-- Observed record includes exactly the first n indexed outcomes. The model
has actual finite observations; Bool indexes two complete predictive laws. -/
abbrev Record (n : Nat) := Fin n → Bool

def prediction (n : Nat) (future : Bool) : Nat → Bool :=
  fun i => if i < n then true else future

def record (n : Nat) (trace : Nat → Bool) : Record n := fun i => trace i

/-- The phase is pre/post observation cutoff. Reuse the existing recoding,
which fixes every measured outcome and complements each later outcome. -/
def recodedTrace (n : Nat) (trace : Nat → Bool) : Nat → Bool :=
  fun i => PredicateRecoding.recode (decide (n ≤ i)) (trace i)

def observed (n : Nat) : Record n := fun _ => true

def finiteRecoding (n : Nat) : Recoding (Record n) Bool :=
  ⟨Equiv.refl _, flip⟩

/-- Compatibility is measured outcome agreement, with no projectibility norm. -/
def compatible (n : Nat) (e : Record n) (h : Bool) : Prop :=
  record n (prediction n h) = e

/-- Recoding commutes with restriction to the observed data, exchanges the two
complete predictions, and therefore forbids a unique neutral choice. Unlike a
finite-prefix counterexample alone, the conclusion constrains selection rules. -/
def FiniteInstantiation : Prop :=
  ∀ n,
    (∀ trace, record n (recodedTrace n trace) = record n trace) ∧
    (∀ h, recodedTrace n (prediction n h) = prediction n (!h)) ∧
    (∀ h, compatible n (observed n) h) ∧
    Neutral (finiteRecoding n) (compatible n) ∧
    prediction n true n ≠ prediction n false n ∧
    (∀ answer, Neutral (finiteRecoding n) answer →
      ∀ h, ¬ SingletonAt answer (observed n) h) ∧
    ¬ (∃ select, Equivariant (finiteRecoding n) select) ∧
    prediction n false = Modern.Hume.Induction.delayedFailure n

/-- Uniform outcome in the supplied measured coordinate, a substantive extra
projectibility criterion. This is not a norm established by observed agreement.
Its transported-coordinate counterpart is a different criterion. -/
def Uniform (trace : Nat → Bool) : Prop := ∀ i j, trace i = trace j

/-- For a nonempty observed prefix, uniformity in the original outcome basis
selects one candidate, whereas applying the same coordinate test after recoding
selects the other. A real measurement/naturalness basis may endorse one test;
that endorsement is additional to representation-neutral finite evidence. -/
def BasisComparison : Prop :=
  ∀ n, 0 < n →
    (∀ h, Uniform (prediction n h) ↔ h = true) ∧
    (∀ h, Uniform (recodedTrace n (prediction n h)) ↔ h = false) ∧
    ¬ Neutral (finiteRecoding n) (fun _ h => Uniform (prediction n h))

/-- Composition with the exact earlier controls preserves the distinction
between coordinate transport, selection, and normative inductive entitlement.
No root-frontier premise or historical attribution is established. -/
def Certificate : Prop :=
  PredicateRecoding.Controls ∧ Modern.Hume.Induction.Checks ∧
  SymmetryConstraint ∧ NoUniqueSelector ∧ Alternatives ∧ FiniteInstantiation ∧
  BasisComparison

end TruthCore.Science.InductionSelection
