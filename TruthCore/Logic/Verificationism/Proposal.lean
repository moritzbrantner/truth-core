module

public import TruthCore.Results.Logic.Verificationism.VerdictSilent.Solution
public import TruthCore.Logic.CorrectionCriterion

/-!
Analyst's V4-style proposal model for #1008; attribution deferred. This is a
bounded reconstruction, not Carnap's complete philosophy. It reuses the existing
two-coordinate comparison language. A proposed object language retains either
one coordinate or both. Relative admissibility is expressive membership, not
pre-theoretic cognitive meaning, Ayer's verification criterion, or ambient truth.
An excluded comparison content has no object-language evaluation (`none`); its
ambient truth value is used only by the comparison metalanguage.

Practical choice minimizes retained coordinate channels among proposals adequate
for a supplied task. Adequacy uses the existing exact-classifier notion. This
pragmatic cost is explicit, not a categorical ought or a sourced efficiency
measure. Changing the task is not observing the hidden coordinate. Adoption is
a distinct action constructor from assertion; no assertion/scope bridge is given.
-/
@[expose] public section

namespace TruthCore.Logic.Verificationism.Proposal

open TruthCore.Results.Logic.Verificationism.VerdictSilent
open TruthCore.Logic.CorrectionCriterion

abbrev World := twoCoordinate.World
abbrev Content := twoCoordinate.Sentence

inductive Framework where
  | empirical
  | expanded
  deriving DecidableEq

/-- Retained representation; the second empirical slot is a fixed filler. -/
def encode : Framework → World → World
  | .empirical, w => (w.1, false)
  | .expanded, w => w

/-- Coordinate channels retained, the stipulated pragmatic complexity measure. -/
def channels : Framework → Nat
  | .empirical => 1
  | .expanded => 2

/-- Computable membership in the proposed Boolean sublanguage. -/
def admitted : Framework → Content → Bool
  | .empirical, s => (s (false, false) == s (false, true)) &&
      (s (true, false) == s (true, true))
  | .expanded, _ => true

def Admitted (f : Framework) (s : Content) : Prop := admitted f s = true

/-- Partial object-language evaluation, distinct from the ambient comparison. -/
def evaluate (f : Framework) (w : World) (s : Content) : Option Bool :=
  if admitted f s then some (s w) else none

def observed : Content := fun w => w.1
def hidden : Content := fun w => w.2
def tautology : Content := fun _ => true

inductive Task where
  | observedQuestion
  | hiddenQuestion
  deriving DecidableEq

def question : Task → Content
  | .observedQuestion => observed
  | .hiddenQuestion => hidden

/-- Extensional task adequacy, not warranted access or psychological ability. -/
def Adequate (f : Framework) (t : Task) : Prop :=
  AdmitsCriterion (encode f) (fun w => question t w = true)

/-- A stipulated pragmatic policy: least channel cost among adequate proposals. -/
def Adopted (t : Task) (f : Framework) : Prop :=
  Adequate f t ∧ ∀ g, Adequate g t → channels f ≤ channels g

inductive Act where
  | adopt (f : Framework)
  | assertContent (s : Content)

def IsAssertion : Act → Prop
  | .adopt _ => False
  | .assertContent _ => True

/-- All membership tests agree with exact representation; both sublanguages
are Boolean closed and include valid contents. -/
def ExpressiveBoundary : Prop :=
  (∀ f s, Admitted f s ↔ AdmitsCriterion (encode f) (fun w => s w = true)) ∧
  (∀ f s, Admitted f s → Admitted f (twoCoordinate.neg s)) ∧
  (∀ f s t, Admitted f s → Admitted f t → Admitted f (twoCoordinate.conj s t)) ∧
  (∀ f s t, Admitted f s → Admitted f t → Admitted f (twoCoordinate.disj s t)) ∧
  (∀ f s, observableFrame.analytic s → Admitted f s)

/-- The one-channel language handles the observed task but not the hidden task;
the two-channel language handles both. Minimal adequate cost selects different
frameworks for these distinct task goals. -/
def PragmaticBoundary : Prop :=
  (∀ t, Adequate .empirical t ↔ t = .observedQuestion) ∧
  (∀ t, Adequate .expanded t) ∧
  (∀ f, Adopted .observedQuestion f ↔ f = .empirical) ∧
  (∀ f, Adopted .hiddenQuestion f ↔ f = .expanded) ∧
  (∀ f, ¬ IsAssertion (.adopt f))

/-- Included content is nontrivial; exclusion admits both ambient truth values.
Neither relative exclusion nor pragmatic adoption settles ambient truth. -/
def SemanticControls : Prop :=
  Admitted .empirical observed ∧ Admitted .empirical tautology ∧
  ¬ Admitted .empirical hidden ∧ ¬ Admitted .empirical (twoCoordinate.neg hidden) ∧
  Admitted .expanded hidden ∧
  evaluate .empirical (false, true) hidden = none ∧
  evaluate .empirical (false, false) hidden = none ∧
  encode .empirical (false, true) = encode .empirical (false, false) ∧
  twoCoordinate.holds (false, true) hidden ∧
  ¬ twoCoordinate.holds (false, false) hidden ∧
  ¬ twoCoordinate.holds (false, true) observed ∧
  twoCoordinate.holds (true, true) observed ∧
  ¬ (∀ s, ¬ Admitted .empirical s → ∀ w, ¬ twoCoordinate.holds w s) ∧
  ¬ (∀ s, Admitted .empirical s) ∧
  (Adopted .observedQuestion .empirical ∧
    twoCoordinate.holds (false, true) hidden ∧ ¬ twoCoordinate.holds (false, false) hidden)

/-- A joint model of the declared proposal reconstruction, composed with the
previous criterion-verdict boundary. No historical completeness or root closure. -/
def JointSurvivor : Prop :=
  ExpressiveBoundary ∧ PragmaticBoundary ∧ SemanticControls ∧ CriterionVerdictSilentOnTruth

end TruthCore.Logic.Verificationism.Proposal
