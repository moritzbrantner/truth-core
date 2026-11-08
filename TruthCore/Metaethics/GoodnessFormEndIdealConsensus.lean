module
public import TruthCore.Metaethics.GoodnessFormEnd
@[expose] public section
namespace TruthCore.Metaethics.GoodnessFormEndIdealConsensus
open GoodnessFormEnd
/-- Ideal assessors are a supplied class, not a claim about real idealization.
Approval may be mistaken. No practical obligation is encoded. -/
structure Assessment (f : Frame) where
  Assessor : Type
  approves : Assessor → f.Being → f.Perfection → Prop

def Consensus {f : Frame} (a : Assessment f) (x : f.Being) (p : f.Perfection) : Prop :=
  ∀ i, a.approves i x p
/-- Open ideal-attitude reduction, independently falsifiable. -/
def Reduction (f : Frame) (a : Assessment f) : Prop :=
  ∀ x p, f.GoodIn x p ↔ Consensus a x p
/-- Open completeness bridge from due actuality to all ideal approvals. -/
def Acceptance (f : Frame) (a : Assessment f) : Prop :=
  ∀ x p, DueActuality f x p → Consensus a x p
/-- Pointwise soundness needs only one assessor for each aspect, not universal
infallibility or a single assessor sound about every aspect. It forces the
assessor class to be inhabited when the aspect domain is inhabited. -/
def SoundWitness (f : Frame) (a : Assessment f) : Prop :=
  ∀ x p, ∃ i, a.approves i x p → DueActuality f x p

def exactAssessment : Assessment artifact := ⟨Unit, fun _ x p => DueActuality artifact x p⟩
def permissive : Assessment surplusArtifact := ⟨Unit, fun _ _ p => artifactHas .knife p⟩
def rejecting : Assessment omissionArtifact := ⟨Unit, fun _ x p => omissionArtifact.GoodIn x p⟩
def empty : Assessment surplusArtifact := ⟨Empty, fun i => nomatch i⟩
/-- Nonvacuity, carrying-premise omissions and empty-consensus trap, all on the
existing nonempty artifact domain; no metaphysical possibility is asserted. -/
def Controls : Prop :=
  (Reduction artifact exactAssessment ∧ Acceptance artifact exactAssessment ∧
    SoundWitness artifact exactAssessment ∧ DueActualityThesis artifact) ∧
  (Reduction surplusArtifact permissive ∧ Acceptance surplusArtifact permissive ∧
    ¬ SoundWitness surplusArtifact permissive ∧ ¬ DueActualityThesis surplusArtifact) ∧
  (Reduction omissionArtifact rejecting ∧ SoundWitness omissionArtifact rejecting ∧
    ¬ Acceptance omissionArtifact rejecting ∧ ¬ DueActualityThesis omissionArtifact) ∧
  (Acceptance surplusArtifact empty ∧ ¬ SoundWitness surplusArtifact empty ∧
    Consensus empty .knife .edge) ∧
  (∃ a : Assessment surplusArtifact, Acceptance surplusArtifact a ∧
    SoundWitness surplusArtifact a ∧ ¬ Reduction surplusArtifact a ∧
    ¬ DueActualityThesis surplusArtifact)
end TruthCore.Metaethics.GoodnessFormEndIdealConsensus
