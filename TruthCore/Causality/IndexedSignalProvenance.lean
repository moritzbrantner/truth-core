/-! Source-free local interfaces for an indexed signal, not an attribution of
all these constraints to Koons's signal revision. PGR's indexed creation and
maintenance motivate a candidate interpretation, subject to faithful detectors,
closed inputs and exact forwarding. Nat indices order the stipulated channel;
no actual causal powers, modal world or existential grounding is represented. -/
namespace TruthCore.Causality.IndexedSignalProvenance

/-- Every output code is either issued at its own numbered station or is
forwarded unchanged from the immediate upstream output. This is a local
conservation/closed-interface assumption, not global origin existence. -/
def LocalConservation (signal : Nat → Option Nat) (issued : Nat → Prop) : Prop :=
  ∀ n j, signal n = some j → (issued n ∧ j = n) ∨ signal (n + 1) = some j

/-- An output's finite code is its own or an earlier station's index. The
upstream direction has increasing indices. This applies to EVERY output,
not just the chosen observation; numeric labeling alone does not enforce it. -/
def IndexAdmissible (signal : Nat → Option Nat) : Prop :=
  ∀ n j, signal n = some j → n ≤ j

/-- Every observed code was issued at its named station. No uniqueness of
issuance, firstness in time, actual existence or efficient cause is asserted. -/
def GlobalProvenance (signal : Nat → Option Nat) (issued : Nat → Prop) : Prop :=
  ∀ n j, signal n = some j → issued j

/-- Same-carrier omission controls, plus a quiet positive control: local
conservation and index admissibility do not require any signal or issuance.
These are formal assignments, not possibilities or actual signal systems. -/
def Controls : Prop :=
  (∃ signal issued, LocalConservation signal issued ∧
    ¬ IndexAdmissible signal ∧ ¬ GlobalProvenance signal issued) ∧
  (∃ signal issued, IndexAdmissible signal ∧
    ¬ LocalConservation signal issued ∧ ¬ GlobalProvenance signal issued) ∧
  (∃ signal issued, LocalConservation signal issued ∧ IndexAdmissible signal ∧
    (∀ n, signal n = none) ∧ (∀ n, ¬ issued n))

end TruthCore.Causality.IndexedSignalProvenance
