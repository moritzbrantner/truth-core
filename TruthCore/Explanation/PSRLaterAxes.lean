module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.NormNum
public import TruthCore.Explanation.PSRSelfApplication
public import TruthCore.Explanation.ExplanatorySymmetry
public import TruthCore.Explanation.StoppingPoints

/-!
# Later PSR axes on the existing comparison arena (#942)

Epistemic support, ontic reason coverage, truth-discriminating contrast, numerical
chance and productive `Supply` retain their different meanings. Probability is a
normalized Mathlib PMF on the SAME arena worlds; it is neither causal power nor
metaphysical possibility. Productive comparisons use the exact existing #735
exercise and its #750 arena projection, not a new causal ontology. See the added
section of `docs/notes/psr-strength-755.md` for interpretation and open bridges.
-/

@[expose] public section

namespace TruthCore.Explanation.PSRLaterAxes

open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.PSRSelfApplication hiding Fact groundInquiry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Causality.DerivativeJointPower
open scoped ENNReal

variable {W B F : Type}

/-- Probability of a fact's truth set under the supplied normalized mass function.
PMF outer measure makes every set measurable; no empirical propensity, causal
relevance or identification of zero mass with impossibility is assumed. -/
noncomputable def chance (μ : PMF W) (A : Arena W B F) (f : F) : ℝ≥0∞ :=
  μ.toOuterMeasure {w | A.holds w f}

/-- The usual event-ratio conditional probability. Interpretation as conditioning
requires a positive denominator, recorded by `Raises` or `PositiveBase`. -/
noncomputable def chanceGiven (μ : PMF W) (A : Arena W B F) (r f : F) : ℝ≥0∞ :=
  μ.toOuterMeasure {w | A.holds w r ∧ A.holds w f} / chance μ A r

/-- Probability raising by the truth of a reason, with positive conditioning mass.
This is association under the supplied distribution, not production or causation. -/
def Raises (μ : PMF W) (A : Arena W B F) (r f : F) : Prop :=
  0 < chance μ A r ∧ chance μ A f < chanceGiven μ A r f

/-- Every base member has positive probability, so all its rankings are genuine
conditional probabilities rather than the totalized zero-denominator ratio. -/
def PositiveBase (μ : PMF W) (A : Arena W B F) (base : F → Prop) : Prop :=
  ∀ r, base r → 0 < chance μ A r

/-- The #742 per-reason ranking specialized to conditional event probabilities.
The distribution and truth assignments are fixed; no outcome-dependent resetting
of the chance law occurs between designated worlds. -/
noncomputable def chanceFrame (μ : PMF W) (A : Arena W B F) : Frame W B F :=
  perReason A (chanceGiven μ A)

/-- A normalized finite distribution on the existing #750 ground's Nat worlds:
world0 has mass3/4, world1 has mass1/4, other worlds have mass0. -/
noncomputable def trial : PMF Nat :=
  (PMF.ofFintype (fun b : Bool => if b then (3 : ℝ≥0∞) / 4 else 1 / 4)
    (by
      rw [Fintype.sum_bool]
      change (3 : ℝ≥0∞) / 4 + 1 / 4 = 1
      rw [← ENNReal.add_div]
      have he : (3 : ℝ≥0∞) + 1 = 4 := by norm_num
      rw [he]
      exact ENNReal.div_self (by norm_num) (by norm_num))).map (fun b => if b then 0 else 1)

/-- Inquiry coverage is not an ontic PSR without the explicit tracking bridge.
With that bridge it reaches the earlier collapse core, not a preferred conclusion.
A consistent critic meets its demands with a supported brute root. -/
def InquiryAxis : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W),
    SupportCoverage A I w → (TrackingBridge A I w ↔ ContingentPSR A w)) ∧
  (∀ (W B F : Type) (A : Arena W B F) (I : Inquiry W F) (w : W) (t c : F),
    SupportCoverage A I w → TrackingBridge A I w → ConjunctSound A → Factive A →
    Necessitating A → Distribution A → IrreflexiveContingent A →
    BCCFAt A w t → Contingent A w c → False) ∧
  (CoreDemanded critic ∧ Honors critic science .a ∧
    BruteAt (scene true) .a .root ∧ Supported science .a .root ∧
    ¬ ContingentPSR (scene true) .a)

/-- Contrast standards have different force: uniform contrast implies per-rival
contrast; reason closure, contingency and foundedness clash with per-rival
contrast. The necessary ground admits a closed two-way account but fails contrast;
the infinite chain with its whole meets per-rival but not uniform contrast. -/
def ContrastAxis : Prop :=
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (S : F → Prop),
    UniformContrast A w S → ContrastRelevant A w S) ∧
  (∀ (W B F : Type) (A : Arena W B F) (w : W) (S : F → Prop) (x : F),
    ReasonClosed A w S x → Contingent A w x → Founded A w S →
    ContrastRelevant A w S → False) ∧
  (ReasonClosed ground 0 OneSource .target ∧ Founded ground 0 OneSource ∧
    TwoWay ground 0 OneSource ∧ ¬ ContrastRelevant ground 0 OneSource) ∧
  (ReasonClosed ExplanatoryAdequacy.chain 0 MembersAndWhole .target ∧
    ContrastRelevant ExplanatoryAdequacy.chain 0 MembersAndWhole ∧
    ¬ UniformContrast ExplanatoryAdequacy.chain 0 MembersAndWhole)

/-- Chance ranking and probability raising are distinct. Truths holding throughout the probability sample space cannot
raise probability by conditioning (modal necessity alone is not that premise). Fixed chance rankings inherit #742's collapse
constraint if every actual field outcome must be net-selected. A normalized 3/4,
1/4 control admits the less likely outcome, without net selection there. A zero
probability event can still be true at an accessible world outside PMF support. -/
def ProbabilityAxis : Prop :=
  (∀ (W B F : Type) (μ : PMF W) (A : Arena W B F) (r f : F),
    (∀ w, A.holds w r) → chance μ A r = 1 ∧
      chanceGiven μ A r f = chance μ A f ∧ ¬ Raises μ A r f) ∧
  (∀ (W B F : Type) (μ : PMF W) (A : Arena W B F) (base O : F → Prop) (a : W) (f : F),
    PositiveBase μ A base → NecessaryBase A base a →
    (∀ w, Worlds A a w → SelectedAt (chanceFrame μ A) base O w) →
    (∀ w, Worlds A a w → ExhaustiveAt A O w) →
    (∀ w, Worlds A a w → ExclusiveAt A O w) → O f → ¬ Contingent A a f) ∧
  (chance trial ground (.source true) = 1 ∧
    chanceGiven trial ground (.source true) .target = 3 / 4 ∧
    chanceGiven trial ground (.source true) .other = 1 / 4 ∧
    PositiveBase trial ground oneSource ∧
    SelectedAt (chanceFrame trial ground) oneSource Rival 0 ∧
    ¬ SelectedAt (chanceFrame trial ground) oneSource Rival 1 ∧
    ground.holds 1 (.source true) ∧ ground.explains 1 (.source true) .other ∧
    ground.holds 1 .other ∧ ¬ ground.holds 1 .target ∧
    0 < chance trial ground .other ∧
    ¬ Raises trial ground (.source true) .target) ∧
  (chance (PMF.pure 0) ground .other = 0 ∧ Access ground 0 1 ∧ ground.holds 1 .other)

/-- At the SAME actual target2, all-necessary overlays all meet contingent PSR and
reason closure, but productive Supply succeeds for single/plural and fails for
branch/chain. The source-free chain even meets unrestricted fact PSR. Plural
Supply does not imply a least graph foundation, and the rooted branch does not
imply Supply. These are projections/derivations, not an adequacy judgment. -/
def ProductiveAxis : Prop :=
  (∀ k, ContingentPSR (overlay k true) false ∧
    ∃ S, ReasonClosed (overlay k true) false S 2) ∧
  (FactPSR (overlay .chain true) false ∧
    ¬ Supply (UltimateAdequacy.groups .chain) (UltimateAdequacy.intrinsic .chain) 2) ∧
  Supply (UltimateAdequacy.groups .single) (UltimateAdequacy.intrinsic .single) 2 ∧
  (Supply (UltimateAdequacy.groups .plural) (UltimateAdequacy.intrinsic .plural) 2 ∧
    ¬ ∃ s, TruthCore.Causality.JointGroups.least (UltimateAdequacy.groups .plural).graph s) ∧
  (TruthCore.Causality.JointGroups.least (UltimateAdequacy.groups .branch).graph 0 ∧
    ¬ Supply (UltimateAdequacy.groups .branch) (UltimateAdequacy.intrinsic .branch) 2)

/-- A norm excluding brute indispensable foundations admits two brute alternative
roots. It exempts an unexplained necessary ground; the unrestricted version does
not. These are the actual #746 verdicts, not a defense of either stopping norm. -/
def StoppingAxis : Prop :=
  (StoppingPoints.NoBruteFoundation StoppingPoints.twinRoots false ∧
    BruteAt StoppingPoints.twinRoots false .left ∧ BruteAt StoppingPoints.twinRoots false .right) ∧
  (StoppingPoints.NoBruteFoundation (PSRStrength.ground false) false ∧
    ¬ StoppingPoints.NoUnreasonedFoundation (PSRStrength.ground false) false)

/-- No tested structural mark settles personal agency: the very same necessary-
base contingent-outcome frame meets all four #742 choice marks with either value
of the supplied personal flag. This is a signature limitation, not a theorem
that personal and impersonal agency are philosophically equivalent. -/
def AgencyBoundary : Prop :=
  Marks acting twoSources Rival 0 ∧ NecessaryBase acting.arena twoSources 0 ∧
  Contingent acting.arena 0 .target ∧
  PersonalStop acting twoSources (fun _ => True) ∧
  ¬ PersonalStop acting twoSources (fun _ => False)

/-- Extends the certified earlier scope/modal/quality map and collapse core by
composed later axes. All comparisons are conditional formal consequences or
named mathematical controls. No PSR, probability interpretation, causal
applicability or personal-ground conclusion is independently established. -/
def InterpretedMap : Prop :=
  StrengthMap ∧ CollapseCore ∧ TruthCore.Explanation.ExistencePSR.PsrScopeBoundary ∧
  InquiryAxis ∧ ContrastAxis ∧ ProbabilityAxis ∧
  ProductiveAxis ∧ StoppingAxis ∧ AgencyBoundary

end TruthCore.Explanation.PSRLaterAxes
