module

public import TruthCore.Causality.NecessarySenseFork
public import TruthCore.Logic.StrengthComparison

/-!
# Certified differences in the necessary-root frame chain (#1598)

The `strengthens` registrations between the frame-class readings of the
necessary-being node (`TruthCore.Causality.NecessarySenseFork`) each relate
two statements of the form "there is a root `n` with the classical facts,
the route's frame satisfies frame class `C`, and `n` exists at every world
accessible from `w`". They differ only in the frame class, so the difference
is a frame condition on the route's frame that does not mention `n`:

* S5 (reflexive and Euclidean) over S4 (reflexive and transitive): the frame is
  symmetric (axiom B); reflexive, transitive and symmetric frames are
  Euclidean, and reflexive Euclidean frames are symmetric.
* KTB (reflexive and symmetric) over KT (reflexive): the frame is symmetric.

Each delta is a named frame condition, not `S`, `W → S`, `W` or `True`. These
are mathematical comparisons inside the fork's encoding; they supply no premise
about which frame class the route's modality has.
-/

@[expose] public section

namespace TruthCore.Logic.Strength.NecessaryFrames

open TruthCore.Modal
open TruthCore.Logic.StrengthComparison
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- Delta: the accessibility relation of the route's modal frame is symmetric
(frame condition B). It says nothing about the root. -/
def RouteFrameSymmetric {W : Type} (σ : Signature) (m : Profile W σ.Being) : Prop :=
  Symmetric m.ontic.frame

/-- S5 node over S4 node, difference: the frame is symmetric. -/
def s5OverS4 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : ComparisonSpec where
  stronger := NecessaryRootBoxS5 σ m w CN
  weaker := NecessaryRootBoxS4 σ m w CN
  delta := RouteFrameSymmetric σ m

/-- Exact factorization: the S5 node holds iff the S4 node holds and the
route's frame is symmetric. -/
def S5OverS4Exact : Prop :=
  ∀ {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W) (CN : σ.Being → σ.Being → Prop),
    NecessaryRootBoxS5 σ m w CN ↔ NecessaryRootBoxS4 σ m w CN ∧ RouteFrameSymmetric σ m

/-- KTB node over T node, difference: the frame is symmetric. -/
def bOverT {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) : ComparisonSpec where
  stronger := NecessaryRootBoxB σ m w CN
  weaker := NecessaryRootBoxT σ m w CN
  delta := RouteFrameSymmetric σ m

/-- Exact factorization: the KTB node holds iff the T node holds and the
route's frame is symmetric. -/
def BOverTExact : Prop :=
  ∀ {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W) (CN : σ.Being → σ.Being → Prop),
    NecessaryRootBoxB σ m w CN ↔ NecessaryRootBoxT σ m w CN ∧ RouteFrameSymmetric σ m

end TruthCore.Logic.Strength.NecessaryFrames
