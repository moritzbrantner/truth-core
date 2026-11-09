module

public import TruthCore.Case.Catholicism.Root

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

/-- Both scopes retain the exact inherited endpoint core. Same-matter revision
supplies distinct judgments; cross-matter replacement retains its primitive act. -/
example {S J M T : Type} (B : T → T → Prop) (m : J → M)
    (E : S → J → T → Prop) (C : J → T → Prop)
    (R : S → J → J → Prop) (s : S) (j k : J) (t u : T) :
    (SameMatterRevision B m E C s j k t u →
      ReplacementConditions B E C (fun _ a b => a ≠ b) s j k t u) ∧
    (CrossMatterReplacement B m E C R s j k t u →
      ReplacementConditions B E C R s j k t u) :=
  ⟨fun h => h.2.2, fun h => h.2.2⟩

/-- A stronger conditional act profile (every cross-matter endpoint transition
is undertaken as replacement) suffices for the primitive act conjunct. It is
an extra assumption, not an analysis inferred from temporal endpoints. -/
example {S J M T : Type} (B : T → T → Prop) (m : J → M)
    (E : S → J → T → Prop) (C : J → T → Prop)
    (R : S → J → J → Prop)
    (undertaken : ∀ s j k t u, m j ≠ m k →
      ReplacementConditions B E C (fun _ _ _ => True) s j k t u → R s j k)
    (s : S) (j k : J) (t u : T) (different : m j ≠ m k)
    (adoption : ¬ E s k t)
    (h : ReplacementConditions B E C (fun _ _ _ => True) s j k t u) :
    CrossMatterReplacement B m E C R s j k t u := by
  exact ⟨different, adoption, h.1, undertaken s j k t u different h, h.2.2⟩

/-- Root-route test: correct-after yields the particular proposition only with
an explicit calibration from the supplied judgment norm to that proposition.
The same test works for either sibling through the inherited core. -/
example {S J T : Type} (B : T → T → Prop)
    (E : S → J → T → Prop) (C : J → T → Prop)
    (R : S → J → J → Prop) (s : S) (j k : J) (t u : T)
    (p : Prop) (h : ReplacementConditions B E C R s j k t u)
    (calibration : C k u → p) : p :=
  calibration h.2.2.2.2.2.2

/-- Strong universal profile for the named root-route step: for EVERY revealed
proposal, an actual correction endpoint representing that proposition plus
truth calibration suffices. One correction cannot supply this universal
coverage. God, attributes and founding hypotheses stay exactly those of Root. -/
example (σ : TruthCore.Case.Catholicism.Signature)
    {S J T : Type} (B : T → T → Prop)
    (E : S → J → T → Prop) (C : J → T → Prop)
    (R : S → J → J → Prop) (Represents : J → Prop → Prop)
    (coverage : ∀ g c, σ.IsGod g → σ.HasClassicalAttributes g →
      σ.FoundedAsTeachingAuthority g c → ∀ p,
      σ.DefinitivelyProposesAsRevealed c p →
      ∃ s j k t u, Represents k p ∧ ReplacementConditions B E C R s j k t u)
    (calibration : ∀ k u p, Represents k p → C k u → p) :
    TruthCore.Case.Catholicism.BridgeGodFoundedAuthorityProposesOnlyTruth σ := by
  intro g c god attributes founded p proposed
  obtain ⟨s, j, k, t, u, represents, h⟩ :=
    coverage g c god attributes founded p proposed
  exact calibration k u p represents h.2.2.2.2.2.2

/-- Even a nonvacuous same-matter revision can coexist with a false target
proposition: supplied correctness does not by itself calibrate truth. -/
example : SameMatterRevision
    (fun t u : Bool => t = false ∧ u = true) (fun _ : Bool => ())
    (fun (_ : Unit) (j t : Bool) => j = t)
    (fun j _ => j = true) () false true false true ∧ ¬ False := by
  simp [SameMatterRevision, ReplacementConditions]

end TruthCore.Logic.CognitiveReplacement
