module

public import TruthCore.Causality.ActualEuclidean

/-!
# Where Euclidean access at the actual world alone can differ from global Euclidean access

Analyst formulation for the modal spine to "God exists" (stage one); attribution
deferred. `ActualEuclidean.EuclideanAt frame w` (local axiom 5 at `w`) is strictly
weaker than global Euclidean access. This module locates the difference.

`TransitiveAt frame w` is local axiom 4 at `w`: whatever is accessible from a
successor of `w` is accessible from `w` ("possibly possible" collapses to
"possible" at the actual world). `EuclideanOnSuccessors frame w` says every
successor of `w` is itself Euclidean.

The theorem `TruthCore.Results.Causality.ActualOnlyEuclidean.euclideanOnSuccessors`
shows: Euclidean access at `w` together with transitivity at `w` gives Euclidean
access at every successor of `w`; it needs no reflexivity hypothesis. It does
not imply global Euclidean access: `Control.appendix` has both local conditions
at `actual` while Euclidean access fails at the unreachable world `far`.

Unverified corollary (no Lean lemma here): local transitivity makes the successor
set closed, so every world reachable from `w` by a finite forward path, including
`w`, is Euclidean. Under both local conditions, a failure of global Euclidean
access therefore lies outside that generated region. A failure of global
Euclidean access with local axiom 5 alone does not force local axiom 4 to fail.
Changing only unreachable worlds cannot change ordinary forward-modal formula
truth at `w`, with the reachable frame and valuation fixed. This semantic
observation does not cover global world quantifiers or globally stated spine
premises; those may constrain unreachable worlds too.

Both controls are STRUCTURAL SURROGATES: `ActualEuclidean.Control.clustered`
witnesses a non-Euclidean successor and failure of transitivity at `actual`;
`appendix` witnesses global failure at an unreachable world while local
transitivity holds. Neither encodes any
rival view's grounding of access (potentialities, representations, tolerance);
they witness only frame-condition independence. Applicability to reality OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.ActualOnlyEuclidean

open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)

/-- Local axiom 4 at `w`: anything accessible from a successor of `w` is
accessible from `w`. Global `TruthCore.Modal.Transitive` is this at every world. -/
def TransitiveAt {W : Type} (frame : TruthCore.Modal.Frame W) (w : W) : Prop :=
  ∀ v z, frame.access w v → frame.access v z → frame.access w z

/-- Every successor of `w` is Euclidean (local axiom 5 holds at each world `w` sees). -/
def EuclideanOnSuccessors {W : Type} (frame : TruthCore.Modal.Frame W) (w : W) : Prop :=
  ∀ v, frame.access w v → EuclideanAt frame v

namespace Control

/-- `actual` and `near` see only themselves; `far` sees itself and `actual`. -/
def appendix : TruthCore.Modal.Frame Place :=
  ⟨fun a b => a = b ∨ (a = Place.far ∧ b = Place.actual)⟩

/-- (1) On `clustered`, Euclidean access at `actual` holds, transitivity at
`actual` fails, and the successor `near` is not Euclidean.
(2) On `appendix`, Euclidean access, transitivity and reflexivity at `actual`
hold, `actual` does not access `far`, and global Euclidean access fails.
Statements about these finite frames only. -/
def Certificate : Prop :=
  (EuclideanAt TruthCore.Causality.ActualEuclidean.Control.clustered Place.actual ∧
    ¬ TransitiveAt TruthCore.Causality.ActualEuclidean.Control.clustered Place.actual ∧
    ¬ EuclideanAt TruthCore.Causality.ActualEuclidean.Control.clustered Place.near) ∧
  (EuclideanAt appendix Place.actual ∧ TransitiveAt appendix Place.actual ∧
    appendix.access Place.actual Place.actual ∧ ¬ appendix.access Place.actual Place.far ∧
    ¬ TruthCore.Modal.Euclidean appendix)

end Control

end TruthCore.Causality.ActualOnlyEuclidean
