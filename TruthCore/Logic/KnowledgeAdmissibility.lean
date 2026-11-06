module

public import TruthCore.Logic.JustificationIntrospection
public import TruthCore.Results.Modal.PossibilityTransfer.Solution

/-!
Analyst comparison #1080; attribution deferred. Candidate descriptions are not
assumed metaphysically possible merely because an epistemic relation admits them.
The supplied physical projection represents ALL physical information only within
this profile; adequacy for actual physics, knowledge and phenomenal concepts is OPEN.

Reuse: existing relational Knows and Frame/Box/Dia, and the certified two-frame
transfer law. HistorySelection already characterizes generic evidence-only
selection: no fiber-invariance theorem is reproved here. Its presence histories
are not phenomenal reports. RigidDesignation separates necessary co-reference
from epistemic identity but has no learning episode or complete physical report.
MindPhysicalism/Intentionality943 concern occurrence kinds/content, not this
report-level supervenience; no equivalence with their physicalist classification.
-/

@[expose] public section
namespace TruthCore.Logic.KnowledgeAdmissibility
open TruthCore.Modal
open TruthCore.Logic.JustificationIntrospection (Knows)
open TruthCore.Modal.PossibilityTransfer (IncludedAt)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- An idealized veridical report update retains exactly the previous alternatives
with the actual report value. This changes information, not the world's facts.
No actual perceptual mechanism or justification is asserted. -/
def observe {W O : Type} (E : Frame W) (report : W → O) : Frame W :=
  ⟨fun w v => E.access w v ∧ report v = report w⟩

/-- Every true predicate of the WHOLE represented physical value is known.
Quantification is over all predicates of that value, not all worldly truths. -/
def AllPhysicalKnown {W P : Type} (E : Frame W) (physical : W → P) (a : W) : Prop :=
  ∀ f : P → Prop, f (physical a) → Knows E (fun v => f (physical v)) a

/-- Actual-relative supervenience: each M-admitted physical duplicate of the
actual description agrees in phenomenal report. This is not reductive identity,
causal determination or an unrestricted global supervenience claim. -/
def SupervenesAt {W P Q : Type} (M : Frame W) (physical : W → P)
    (phenomenal : W → Q) (a : W) : Prop :=
  Box M (fun v => physical v = physical a → phenomenal v = phenomenal a) a

/-- A metaphysically ADMITTED physical duplicate with a different phenomenal
report, not merely an epistemic description or a derivation of actual dualism. -/
def PhenomenalTwin {W P Q : Type} (M : Frame W) (physical : W → P)
    (phenomenal : W → Q) (a : W) : Prop :=
  Dia M (fun v => physical v = physical a ∧ phenomenal v ≠ phenomenal a) a

/-- Minimal explicit conditional bridge, using known equality of the physical
report rather than assuming every physical predicate known. Inclusion E ⊆ M at
the actual description is the disputed ideal-reflection/admissibility input.
None of these universally quantified inputs is asserted for an actual subject. -/
def AdmissibilityLaw : Prop :=
  ∀ (W P Q : Type) (E M : Frame W) (physical : W → P) (phenomenal : W → Q) (a : W),
    SupervenesAt M physical phenomenal a →
    Knows E (fun v => physical v = physical a) a →
    IncludedAt E M a → Knows E (fun v => phenomenal v = phenomenal a) a

/-- Both bits are description coordinates, not two kinds of substance. -/
abbrev Description := Bool × Bool

def actual : Description := (false, false)
def physical : Description → Bool := Prod.fst
def phenomenal : Description → Bool := Prod.snd

/-- Complete information about the represented physical coordinate. -/
def epistemic : Frame Description :=
  ⟨fun w v => physical v = physical w⟩
def experienced : Frame Description := observe epistemic phenomenal

/-- At diagonal actual, only diagonal descriptions are M-admitted. The other
component makes this relation an equivalence on the entire candidate carrier;
it is not a claim that off-diagonal descriptions are possible at actual. -/
def supervenient : Frame Description :=
  ⟨fun w v => (physical v = phenomenal v ↔ physical w = phenomenal w)⟩

/-- Rival permits physical duplicates to differ phenomenally. -/
def independent : Frame Description := ⟨fun _ _ => True⟩

/-- One fixed, nonvacuous epistemic learning episode, common to both profiles.
Knowledge is factive by reflexivity; initial ignorance is of the same predicate
that becomes known, not merely of a new sentence or name for an old predicate. -/
def SharedEpisode : Prop :=
  Reflexive epistemic ∧ Symmetric epistemic ∧ Transitive epistemic ∧
  Reflexive experienced ∧ Symmetric experienced ∧ Transitive experienced ∧
  AllPhysicalKnown epistemic physical actual ∧
  AllPhysicalKnown experienced physical actual ∧
  Knows epistemic (fun v => physical v = physical actual) actual ∧
  ¬ Knows epistemic (fun v => phenomenal v = phenomenal actual) actual ∧
  Knows experienced (fun v => phenomenal v = phenomenal actual) actual

/-- New knowledge with actual-relative physical supervenience and no admitted
phenomenal twin. A different physical report is admitted, so this is not modal
collapse or a vacuous empty component. The inclusion bridge fails. -/
def SupervenientSurvivor : Prop :=
  Reflexive supervenient ∧ Symmetric supervenient ∧ Transitive supervenient ∧
  SupervenesAt supervenient physical phenomenal actual ∧
  Dia supervenient (fun v => physical v ≠ physical actual) actual ∧
  ¬ PhenomenalTwin supervenient physical phenomenal actual ∧
  ¬ IncludedAt epistemic supervenient actual

/-- Same learning episode, but the candidate physical twin is M-admitted;
the inclusion bridge holds and actual-relative supervenience fails. -/
def TwinRival : Prop :=
  Reflexive independent ∧ Symmetric independent ∧ Transitive independent ∧
  IncludedAt epistemic independent actual ∧
  PhenomenalTwin independent physical phenomenal actual ∧
  ¬ SupervenesAt independent physical phenomenal actual

/-- The general bridge and the two rival profiles on the SAME actual facts,
reports, epistemic relation and update. Neither profile is established actual
metaphysics, nor does learning alone establish nonphysical facts or substances. -/
def Certificate : Prop :=
  AdmissibilityLaw ∧ SharedEpisode ∧ SupervenientSurvivor ∧ TwinRival

end TruthCore.Logic.KnowledgeAdmissibility
