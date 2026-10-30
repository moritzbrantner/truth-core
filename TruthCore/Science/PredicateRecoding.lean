/-! A stipulated two-phase, two-feature recoding control, motivated by the
provisional caption reading documented in docs/notes/carneades-induction.md.
This is not an attributed formalization of Goodman or Swinburne. The phase is
merely a Boolean partition; it does not encode examination history, real color,
physical time or a criterion of inductive entitlement. -/
namespace TruthCore.Science.PredicateRecoding

/-- At each fixed phase the feature coding is its own inverse. -/
def recode (phase feature : Bool) : Bool :=
  if phase then !feature else feature

/-- Independence holds the supplied feature coordinate fixed while varying
phase. Selecting that coordinate as physically relevant is an open commitment. -/
def PhaseIndependent (p : Bool → Bool → Bool) : Prop :=
  ∀ feature, p false feature = p true feature

/-- Change coordinates for the same predicate, using the inverse recoding. -/
def transported (p : Bool → Bool → Bool) (phase codedFeature : Bool) : Bool :=
  p phase (recode phase codedFeature)

/-- The base feature predicate has no phase dependence in the supplied basis. -/
def base (_phase feature : Bool) : Bool := feature

/-- Recoverability and extensional equivalence do not preserve the syntactic
coordinate test of phase independence. Factorization supplies the exact
criterion in the original basis, not a defense of that basis's epistemic role. -/
def Controls : Prop :=
  (∀ phase feature, recode phase (recode phase feature) = feature) ∧
  (∀ p phase feature, transported p phase (recode phase feature) = p phase feature) ∧
  (∀ p, PhaseIndependent p ↔ ∃ q : Bool → Bool, ∀ phase feature,
    p phase feature = q feature) ∧
  PhaseIndependent base ∧ ¬ PhaseIndependent (transported base)

end TruthCore.Science.PredicateRecoding
