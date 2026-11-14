module

public import TruthCore.Logic.GlobalThesisBoundaries

/-!
Analyst formulation, attribution deferred except where a corpus claim says
otherwise: Street's Darwinian dilemma extended to epistemic evaluative
judgments (#1585). Sharon Street, *A Darwinian Dilemma for Realist Theories of
Value* (2006), n. 2 (p. 156) and n. 57 (pp. 163–164), says she thinks the
dilemma can be extended to realism about epistemic reasons, and that her reply
to its self-application against antirealism assumes that an alien investigator
shares our judgments about epistemic reasons. She does not argue the extension
there; the predicates below are the analyst's reconstruction.

A `DarwinianProfile` fixes one scoped epistemic evaluative judgment (for
example "this kind of perceptual seeming counts in favor of believing what it
presents"). Its scenarios share or differ in selective history; the actual
scenario is designated. `verdict` is whether the judgment endorses the content
in a scenario and `correct` whether that content is correct there. Four
outcomes are kept apart:

* origin information: the verdict is fixed by the selective history;
* tracking failure: some scenario with the actual history has an incorrect
  verdict (`HistoryMateMismatch`); it does not entail actual inaccuracy,
  although actual inaccuracy is a special case of it;
* justified defeat: an evidential basis is undercut for a subject, reusing
  `GlobalThesisBoundaries.ReliabilityFrame`;
* rejection of epistemic norms: global epistemic nihilism (`EpistemicReasons`),
  which none of these premises states.

Two readings of the first ("no relation") horn are kept apart. Street's own
horn (pp. 121–122, the Bermuda analogy) holds the realist's truths fixed and
lets the judgments vary with the selective pressure, then argues by a
coincidence step that the actual judgments are in all likelihood off track.
`CorrectnessConstant`, `VerdictVariesAcrossHistories` and `ScenarioMismatch`
encode its non-probabilistic part. The
within-history-variation reading (`CorrectnessVariesWithinHistory`) is an
analyst variant, not her horn. No probability, causal mechanism or actual
selective history is encoded.
-/

@[expose] public section

namespace TruthCore.Logic.DarwinianEpistemicDebunking

open TruthCore.Logic.GlobalThesisBoundaries

/-- Scenarios, their selective histories, a designated actual scenario, and
for one scoped epistemic evaluative judgment its verdict and the correctness
of its content in each scenario. -/
structure DarwinianProfile where
  Scenario : Type
  History : Type
  history : Scenario → History
  actual : Scenario
  verdict : Scenario → Bool
  correct : Scenario → Bool

/-- The scenario has the same selective history as the actual scenario. -/
def HistoryMate (P : DarwinianProfile) (s : P.Scenario) : Prop :=
  P.history s = P.history P.actual

/-- Origin information in its idealized strong form: every scenario with the
actual selective history returns the actual verdict. Street's "tremendous
influence" is weaker; this full fixing is an analyst idealization. -/
def SelectionFixesVerdict (P : DarwinianProfile) : Prop :=
  ∀ s, HistoryMate P s → P.verdict s = P.verdict P.actual

/-- Analyst within-history-variation reading, not Street's horn: some scenario
with the actual selective history differs from the actual scenario in the
correctness of the content. A realism whose correctness is the same in every
scenario fails this premise, although it is the paradigm target of Street's
horn. -/
def CorrectnessVariesWithinHistory (P : DarwinianProfile) : Prop :=
  ∃ s, HistoryMate P s ∧ P.correct s ≠ P.correct P.actual

/-- Correctness is the same in every scenario with the actual selective
history. Constructivist and functional accounts can each supply this for
different reasons. A necessitarian realism satisfies it formally, but survives
through it only given actual accuracy, which Street's horn disputes. -/
def CorrectnessFixedByHistory (P : DarwinianProfile) : Prop :=
  ∀ s, HistoryMate P s → P.correct s = P.correct P.actual

/-- The verdict is correct in the actual scenario. -/
def ActuallyAccurate (P : DarwinianProfile) : Prop :=
  P.verdict P.actual = P.correct P.actual

/-- Tracking failure: some scenario with the actual selective history has an
incorrect verdict. It does not entail inaccuracy in the actual scenario, but
the actual scenario is a history-mate, so actual inaccuracy is a case of it. -/
def HistoryMateMismatch (P : DarwinianProfile) : Prop :=
  ∃ s, HistoryMate P s ∧ P.verdict s ≠ P.correct s

/-- The verdict is correct in every scenario with the actual selective
history. -/
def HistoryMatesAccurate (P : DarwinianProfile) : Prop :=
  ∀ s, HistoryMate P s → P.verdict s = P.correct s

/-- Street's fixed destination: the content's correctness is the same in every
scenario, whatever the selective history. -/
def CorrectnessConstant (P : DarwinianProfile) : Prop :=
  ∀ s, P.correct s = P.correct P.actual

/-- Selection pushes elsewhere: some scenario with a different selective
history returns a different verdict from the actual one. -/
def VerdictVariesAcrossHistories (P : DarwinianProfile) : Prop :=
  ∃ s, P.history s ≠ P.history P.actual ∧ P.verdict s ≠ P.verdict P.actual

/-- The verdict is incorrect in some scenario, which may have another
selective history. -/
def ScenarioMismatch (P : DarwinianProfile) : Prop :=
  ∃ s, P.verdict s ≠ P.correct s

/-- The debunker's defeat policy, applied uniformly: for each basis of the
subject, a tracking failure of the epistemic judgment that basis delivers
undercuts that basis for the subject. `prof` assigns each basis the profile of
its judgment. Because the actual scenario is a history-mate, the policy also
treats an actually false verdict as undercutting: it does not by itself keep
actual inaccuracy and justified defeat apart. -/
def UniformMismatchPolicy (f : ReliabilityFrame) (a : f.Agent)
    (prof : f.Basis → DarwinianProfile) : Prop :=
  ∀ E, HistoryMateMismatch (prof E) → f.undercuts a E

/-- One history and two scenarios, the true one actual. The verdict is always
true and correctness is the scenario label. -/
def originOnly : DarwinianProfile where
  Scenario := Bool
  History := Unit
  history := fun _ => ()
  actual := true
  verdict := fun _ => true
  correct := id

/-- Verdict equals correctness in both scenarios of one history. -/
def tracking : DarwinianProfile where
  Scenario := Bool
  History := Unit
  history := fun _ => ()
  actual := true
  verdict := id
  correct := id

/-- Verdict and correctness are both always true in one history. -/
def fixedTrue : DarwinianProfile where
  Scenario := Bool
  History := Unit
  history := fun _ => ()
  actual := true
  verdict := fun _ => true
  correct := fun _ => true

/-- Basis `true` (the subject's epistemic evaluative basis) gets the
`originOnly` profile in the realist case; basis `false` gets `fixedTrue`. -/
def realistProfiles : Bool → DarwinianProfile := fun E => if E then originOnly else fixedTrue

/-- The existing targeted reliability control: content and basis `true` are
read as the debunking conclusion and the subject's epistemic evaluative basis,
which is undercut; content `false` has undefeated support from basis `false`. -/
def realistFrame : ReliabilityFrame := reliabilityControl true true false

/-- The existing control with no concern and no defeat: nothing is undercut
and every content is warranted. -/
def survivorFrame : ReliabilityFrame := reliabilityControl false false false

/-- Finite controls. (1) Origin fixing and within-history variation give a
tracking failure while the actual verdict is accurate. (2) One omission
example: with variation but no origin fixing, every history-mate is accurate,
so origin fixing is needed. (3) With correctness fixed by history, an actually
accurate selection-fixed verdict has no tracking failure. (4) Realist
self-application: in the existing targeted reliability control, the uniform
policy, sole-basis and warrant conditions hold, the debunking conclusion
(content `true`) lacks warrant while true, and thin F6 holds as undefeated
support for other content. (5) A no-undercutting model with history-fixed
correctness for every basis: the same policy, sole-basis and warrant
conditions hold and the conclusion is warranted. It fits constructivist,
functional and necessitarian-realist readings alike. -/
def DarwinianDebunkingControls : Prop :=
  (SelectionFixesVerdict originOnly ∧ CorrectnessVariesWithinHistory originOnly ∧
    ActuallyAccurate originOnly ∧ HistoryMateMismatch originOnly) ∧
  (¬ SelectionFixesVerdict tracking ∧ CorrectnessVariesWithinHistory tracking ∧
    HistoryMatesAccurate tracking) ∧
  (SelectionFixesVerdict fixedTrue ∧ CorrectnessFixedByHistory fixedTrue ∧
    ActuallyAccurate fixedTrue ∧ ¬ HistoryMateMismatch fixedTrue) ∧
  (UniformMismatchPolicy realistFrame () realistProfiles ∧
    SelectionFixesVerdict (realistProfiles true) ∧
    CorrectnessVariesWithinHistory (realistProfiles true) ∧
    SoleSupportingBasis realistFrame () true true ∧
    WarrantNeedsUndefeatedSupport realistFrame () true ∧
    LacksTargetWarrant realistFrame () true ∧ realistFrame.holds true ∧
    TruthCore.Logic.EpistemicReasons.ThereAreEpistemicReasons (UndefeatedSupport realistFrame)) ∧
  (UniformMismatchPolicy survivorFrame () (fun _ => fixedTrue) ∧
    SelectionFixesVerdict fixedTrue ∧ CorrectnessFixedByHistory fixedTrue ∧
    SoleSupportingBasis survivorFrame () true true ∧
    WarrantNeedsUndefeatedSupport survivorFrame () true ∧ survivorFrame.warranted () true)

/-- Two histories, one scenario each, the true one actual. Correctness is
always true; the verdict follows the history. -/
def crossHistory : DarwinianProfile where
  Scenario := Bool
  History := Bool
  history := id
  actual := true
  verdict := id
  correct := fun _ => true

/-- Controls for the cross-history horn. (1) In `crossHistory` the truth is
fixed and the verdict varies across histories, so some scenario is wrong,
while the actual verdict is accurate, no history-mate is wrong and
correctness does not vary within the actual history: the within-history
reading misses this paradigm fixed-truth case. (2) Omission: with the truth
fixed and only one history, `fixedTrue` has no varying verdict and no
mismatch. -/
def CrossHistoryControls : Prop :=
  (CorrectnessConstant crossHistory ∧ VerdictVariesAcrossHistories crossHistory ∧
    ScenarioMismatch crossHistory ∧ ActuallyAccurate crossHistory ∧
    ¬ HistoryMateMismatch crossHistory ∧ ¬ CorrectnessVariesWithinHistory crossHistory) ∧
  (CorrectnessConstant fixedTrue ∧ ¬ VerdictVariesAcrossHistories fixedTrue ∧
    ¬ ScenarioMismatch fixedTrue)

end TruthCore.Logic.DarwinianEpistemicDebunking
