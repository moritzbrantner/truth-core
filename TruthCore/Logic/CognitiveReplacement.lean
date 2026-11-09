module

/-! Analyst formulation, attribution deferred. Shared necessary conditions for
completed cognitive replacement. This is deliberately not the binding of
CORRECTION_2: same-matter and cross-matter replacement remain distinct options.
The supplied history describes actual endorsement, not possible belief; Before
is actual strict temporal precedence, and Correct is a supplied judgment norm.
Neither correctness nor temporal precedence is certified by a report/criterion.
-/

@[expose] public section
namespace TruthCore.Logic.CognitiveReplacement

/-- An actual later endorsement replaces an earlier erroneous endorsement by
this subject only if the old endorsement is withdrawn. `Replaces` supplies the
interpretive link between the two judgments (e.g. revision on the same matter);
it cannot alone make a transition qualify. Correctness is relative to the
supplied norm at each endpoint. No truth, warrant, authority, causation,
permanence, exclusivity of other beliefs, or need-to-accomplishment is inferred.
This is a common core pending the original sense's replacement-scope decision. -/
def ReplacementConditions {Subject Judgment Time : Type}
    (Before : Time → Time → Prop)
    (Endorses : Subject → Judgment → Time → Prop)
    (Correct : Judgment → Time → Prop)
    (Replaces : Subject → Judgment → Judgment → Prop)
    (subject : Subject) (old new : Judgment) (earlier later : Time) : Prop :=
  Before earlier later ∧ Replaces subject old new ∧
  Endorses subject old earlier ∧ ¬ Correct old earlier ∧
  ¬ Endorses subject old later ∧ Endorses subject new later ∧ Correct new later

/-- A finite witness for the common core: a subject withdraws false and endorses
true at the later of two occasions. This is a model of supplied predicates,
not an instance attributed to any historical subject. -/
example : ReplacementConditions
    (fun t u : Bool => t = false ∧ u = true)
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun (j : Bool) (_ : Bool) => j = true)
    (fun (_ : Unit) (j k : Bool) => j ≠ k)
    () false true false true := by
  simp [ReplacementConditions]

/-- Merely adding a correct judgment while retaining the erroneous one fails. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun _ _ _ => True)
      (fun j _ => j = true) Replaces () false true false true := by
  intro h
  exact h.2.2.2.2.1 trivial

/-- An unrelated later correct belief cannot qualify when the replacement
interpretation supplies no link, even if the other endpoint data fit. -/
example (Before : Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun j _ => j = true) (fun _ _ _ => False) () false true false true := by
  intro h
  exact h.2.1

/-- A replacement link alone supplies neither a temporal transition nor beliefs. -/
example (Endorses : Unit → Bool → Bool → Prop) (Correct : Bool → Bool → Prop) :
    ¬ ReplacementConditions (fun _ _ => False) Endorses Correct
      (fun _ _ _ => True) () false true false true := by
  intro h
  exact h.1

/-- Changed endorsement with no erroneous starting judgment is not correction. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun _ _ => True) Replaces () false true false true := by
  intro h
  exact h.2.2.2.1 trivial

/-- Changed endorsement without correctness afterward also fails. -/
example (Before : Bool → Bool → Prop) (Replaces : Unit → Bool → Bool → Prop) :
    ¬ ReplacementConditions Before (fun (_ : Unit) (j t : Bool) => j = t)
      (fun _ _ => False) Replaces () false true false true := by
  intro h
  exact h.2.2.2.2.2.2

end TruthCore.Logic.CognitiveReplacement

namespace TruthCore.Logic.CognitiveReplacement

/-- Same-subject, same-matter revision. Matter identifies the question judged,
not the verdict: opposite verdicts can concern the same question. Endorsement
is actual history; the new verdict was not endorsed at the earlier endpoint. No additional replacement flag is used: withdrawal of the
erroneous verdict and adoption of the correct verdict on that question at a
strictly later occasion constitute this analyst reading. Supplied temporal,
matter and correctness interpretations remain open applicability inputs. -/
def SameMatterRevision {Subject Judgment Matter Time : Type}
    (Before : Time → Time → Prop) (MatterOf : Judgment → Matter)
    (Endorses : Subject → Judgment → Time → Prop)
    (Correct : Judgment → Time → Prop)
    (subject : Subject) (old new : Judgment) (earlier later : Time) : Prop :=
  MatterOf old = MatterOf new ∧ ¬ Endorses subject new earlier ∧
  ReplacementConditions Before Endorses Correct (fun _ j k => j ≠ k)
    subject old new earlier later

/-- Cross-matter replacement is a separate analyst reading. `ReplacementAct`
is an explicitly primitive relation: this subject undertakes the adoption of
this new judgment as a replacement for this old judgment, rather than merely
having two temporally separated beliefs. Its independent semantic recognition
is OPEN; endpoint data do not define or entail it. One subject indexes both
actual endorsements and the act; unequal matters distinguish this reading.
No causal, normative, epistemic or truth-authority properties are assumed. -/
def CrossMatterReplacement {Subject Judgment Matter Time : Type}
    (Before : Time → Time → Prop) (MatterOf : Judgment → Matter)
    (Endorses : Subject → Judgment → Time → Prop)
    (Correct : Judgment → Time → Prop)
    (ReplacementAct : Subject → Judgment → Judgment → Prop)
    (subject : Subject) (old new : Judgment) (earlier later : Time) : Prop :=
  MatterOf old ≠ MatterOf new ∧ ¬ Endorses subject new earlier ∧
  ReplacementConditions Before Endorses Correct ReplacementAct
    subject old new earlier later

/-- Positive same-question reversal; Bool judgments are opposite verdicts on
one Unit matter, not two different questions. -/
example : SameMatterRevision
    (fun t u : Bool => t = false ∧ u = true) (fun _ : Bool => ())
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun j _ => j = true) () false true false true := by
  simp [SameMatterRevision, ReplacementConditions]

/-- A cross-question witness requires a separately supplied replacement act. -/
example : CrossMatterReplacement
    (fun t u : Bool => t = false ∧ u = true) (fun j : Bool => j)
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun j _ => j = true) (fun _ j k => j = false ∧ k = true)
    () false true false true := by
  simp [CrossMatterReplacement, ReplacementConditions]

/-- The two scoped readings cannot classify the same endpoints together. -/
example {S J M T : Type} (B : T → T → Prop) (m : J → M)
    (E : S → J → T → Prop) (C : J → T → Prop)
    (R : S → J → J → Prop) (s : S) (j k : J) (t u : T)
    (h : SameMatterRevision B m E C s j k t u) :
    ¬ CrossMatterReplacement B m E C R s j k t u := by
  intro cross
  exact cross.1 h.1

/-- Correct later belief, error before and withdrawal still do not supply the
cross-matter replacement act. -/
example : ¬ CrossMatterReplacement
    (fun t u : Bool => t = false ∧ u = true) (fun j : Bool => j)
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun j _ => j = true) (fun _ _ _ => False)
    () false true false true := by
  intro h
  exact h.2.2.2.1

/-- Adoption by someone else cannot complete this subject's revision. -/
example (B : Bool → Bool → Prop) (C : Bool → Bool → Prop) :
    ¬ SameMatterRevision B (fun _ : Bool => ())
      (fun s j t : Bool => s = false ∧ j = false ∧ t = false ∨
        s = true ∧ j = true ∧ t = true)
      C false false true false true := by
  simp [SameMatterRevision, ReplacementConditions]

/-- A supplied norm and a need for revision do not give an actual adoption. -/
example (B : Bool → Bool → Prop) (C : Bool → Bool → Prop) :
    ¬ SameMatterRevision B (fun _ : Bool => ())
      (fun (_ : Unit) (j t : Bool) => j = false ∧ t = false)
      C () false true false true := by
  simp [SameMatterRevision, ReplacementConditions]

/-- Continuing to endorse the erroneous judgment prevents revision. -/
example (B : Bool → Bool → Prop) (C : Bool → Bool → Prop) :
    ¬ SameMatterRevision B (fun _ : Bool => ())
      (fun (_ : Unit) (j t : Bool) => j = false ∨ t = true)
      C () false true false true := by
  simp [SameMatterRevision, ReplacementConditions]

/-- A correct judgment already held earlier is not newly adopted here. -/
example (B : Bool → Bool → Prop) (C : Bool → Bool → Prop) :
    ¬ SameMatterRevision B (fun _ : Bool => ())
      (fun (_ : Unit) (j t : Bool) => j = true ∨ t = false)
      C () false true false true := by
  simp [SameMatterRevision, ReplacementConditions]

end TruthCore.Logic.CognitiveReplacement
