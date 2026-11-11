module

public import TruthCore.Logic.EpistemicReasons
public import TruthCore.Logic.ObjectiveTruthDefinitionFork
public import TruthCore.Logic.SelfApplication
public import TruthCore.Logic.Verificationism

/-!
Analyst formulations for three global theses. Scope, classification, epistemic
dependence and transmission are explicit. The formulations carry no historical
attribution, probability judgment or independent warrant.
-/

@[expose] public section

namespace TruthCore.Logic.GlobalThesisBoundaries

open TruthCore.Logic.EpistemicReasons
open TruthCore.Logic.ObjectiveTruthDefinitionFork
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Verificationism

/-- The empirical-only criterion. Cognitive meaningfulness is an independently
supplied predicate. The empirical verifiability predicate is supplied by the
selected test, with no separate analytic exception. -/
def StrictVerification {L : Language}
    (meaningful scope verifiable : L.Sentence → Prop) : Prop :=
  (Norm.mk scope verifiable).Holds meaningful

/-- The formulation of the strict criterion lies within its own scope. -/
def StrictFormulationInScope {L : Language} (scope : L.Sentence → Prop)
    (self : L.Sentence) : Prop :=
  PrincipleInOwnScope (L := L) scope self

/-- The formulation of the strict criterion fails the selected empirical test. -/
def StrictFormulationNotVerifiable {L : Language} (verifiable : L.Sentence → Prop)
    (self : L.Sentence) : Prop :=
  PrincipleNotVerifiable (L := L) verifiable self

/-- The strict criterion's two self-application consequences at its own
formulation. Adoption as a proposal has no built-in scope premise. -/
def StrictVerificationDilemma {L : Language}
    (meaningful scope verifiable : L.Sentence → Prop) (self : L.Sentence) : Prop :=
  (StrictVerification (L := L) meaningful scope verifiable → ¬ meaningful self) ∧
    (meaningful self → ¬ StrictVerification (L := L) meaningful scope verifiable)

/-! ### Social construction and truth status -/

/-- Every actually true content in scope has a social construction status.
The construction classifier is primitive, independent of truth evaluation.
It can classify contents by their social origin or conventions of expression,
which need not vary the truth of the same content. -/
def ScopedSocialConstruction (f : ObjectiveTruthDefinitionFork.Frame)
    (scope constructed : f.Sentence → Prop) : Prop :=
  ∀ s, scope s → f.holds f.actual s → constructed s

/-- Truth-dependence bridge, only for actually true constructed contents in
scope: changing the supplied attitude profile can make the same content fail
to hold. Whether the supplied profiles vary only the relevant social attitudes
or conventions is an independent application question. -/
def ConstructionVariesTruth (f : ObjectiveTruthDefinitionFork.Frame)
    (scope constructed : f.Sentence → Prop) : Prop :=
  ∀ s, scope s → constructed s → f.holds f.actual s → ∃ p, ¬ f.holds p s

/-- No content inside the stated scope is classified as objectively true.
This says nothing about the classifier outside that scope. -/
def NoObjectiveTruthInScope (f : ObjectiveTruthDefinitionFork.Frame)
    (scope : f.Sentence → Prop) : Prop :=
  ∀ s, scope s → ¬ f.objective s

/-- The local control scopes only the actual-true, variable content. -/
def socialLocal (s : ObjectiveTruthDefinitionFork.Content) : Prop :=
  s = .actualTrueVariable

/-- The local scope can contain genuinely variable truth while a stable true
content survives outside. The global construction classifier also permits
stable true content in scope when the truth-dependence bridge fails. -/
def SocialConstructionControls : Prop :=
  ActualStableDefinition actualStable ∧
    (ScopedSocialConstruction actualStable socialLocal socialLocal ∧
      ConstructionVariesTruth actualStable socialLocal socialLocal ∧
      socialLocal .actualTrueVariable ∧ actualStable.holds actualStable.actual .actualTrueVariable ∧
      ¬ socialLocal .stableTrue ∧ actualStable.objective .stableTrue) ∧
    (ScopedSocialConstruction actualStable (fun _ => True) (fun _ => True) ∧
      ¬ ConstructionVariesTruth actualStable (fun _ => True) (fun _ => True) ∧
      ¬ NoObjectiveTruthInScope actualStable (fun _ => True))

/-! ### Reliability concern and warrant transmission -/

/-- One assessment of one subject's evidential bases. Low assessment and
inability to assess record distinct kinds of concern about the reliability
of a basis, without identifying them with actual unreliability. An undercut
basis fails as evidential support without asserting the falsity of any of its
contents. Warrant and truth are independent data. The supplied basis roster
determines how broadly support is assessed. -/
structure ReliabilityFrame where
  Agent : Type
  Content : Type
  Basis : Type
  accepts : Agent → Content → Prop
  assessesLow : Agent → Basis → Prop
  cannotAssess : Agent → Basis → Prop
  supports : Agent → Basis → Content → Prop
  undercuts : Agent → Basis → Prop
  warranted : Agent → Content → Prop
  holds : Content → Prop

/-- The subject accepts the specified worldview package. -/
def AcceptedPackage (f : ReliabilityFrame) (a : f.Agent) (package : f.Content) : Prop :=
  f.accepts a package

/-- Conditional reliability assessment of a specified basis given acceptance
of the package. Its conclusion can be either a low assessment or inability
to assess. Neither disjunct follows from naturalism or evolution alone here. -/
def PackageRaisesReliabilityConcern (f : ReliabilityFrame) (a : f.Agent)
    (package : f.Content) (basis : f.Basis) : Prop :=
  f.accepts a package → f.assessesLow a basis ∨ f.cannotAssess a basis

/-- An explicit defeater policy for the subject and basis. A proponent can
reject this policy in particular for inability to assess reliability. -/
def ReliabilityConcernUndercuts (f : ReliabilityFrame) (a : f.Agent) (basis : f.Basis) : Prop :=
  (f.assessesLow a basis ∨ f.cannotAssess a basis) → f.undercuts a basis

/-- The specified basis is undercut for the subject. -/
def BasisUndercut (f : ReliabilityFrame) (a : f.Agent) (basis : f.Basis) : Prop :=
  f.undercuts a basis

/-- Every available supporting basis for this content is the targeted basis.
This allows other contents to have independent supporting bases. -/
def SoleSupportingBasis (f : ReliabilityFrame) (a : f.Agent) (p : f.Content)
    (basis : f.Basis) : Prop :=
  ∀ b, f.supports a b p → b = basis

/-- The subject has at least one supporting basis for the content that has
not been undercut. -/
def UndefeatedSupport (f : ReliabilityFrame) (a : f.Agent) (p : f.Content) : Prop :=
  ∃ b, f.supports a b p ∧ ¬ f.undercuts a b

/-- An explicit warrant condition for the specified subject and content. This
is a necessity direction only, and warrant can remain distinct from support. -/
def WarrantNeedsUndefeatedSupport (f : ReliabilityFrame) (a : f.Agent) (p : f.Content) : Prop :=
  f.warranted a p → UndefeatedSupport f a p

/-- The subject lacks warrant for the targeted content. The content itself
may still be true. -/
def LacksTargetWarrant (f : ReliabilityFrame) (a : f.Agent) (p : f.Content) : Prop :=
  ¬ f.warranted a p

/-- A single subject, two contents and two bases. The Boolean label true
denotes the package or its cognitive basis, and false denotes the other
content or basis. The three flags vary the reliability concern, policy
outcome and presence of independent support for the package. Other-content
support remains intact. -/
def reliabilityControl (concern defeat independent : Bool) : ReliabilityFrame where
  Agent := Unit
  Content := Bool
  Basis := Bool
  accepts := fun _ p => p = true
  assessesLow := fun _ b => b = true ∧ concern = true
  cannotAssess := fun _ _ => False
  supports := fun _ b p => (b = true ∧ p = true) ∨ (b = false ∧ (p = false ∨ independent = true))
  undercuts := fun _ b => b = true ∧ defeat = true
  warranted := fun _ p => p = false ∨ defeat = false ∨ independent = true
  holds := fun _ => True

/-- A local undercutter can coexist with the truth of the package and thin
F6 interpreted by the existence of undefeated support for other content.
Independent support, an omitted reliability assessment, and an omitted
defeater policy each supply a warrant-preserving control. -/
def ReliabilityControls : Prop :=
  let targeted := reliabilityControl true true false
  let supported := reliabilityControl true true true
  let noConcern := reliabilityControl false false false
  let policyRejected := reliabilityControl true false false
  (AcceptedPackage targeted () true ∧
    PackageRaisesReliabilityConcern targeted () true true ∧
    ReliabilityConcernUndercuts targeted () true ∧
    SoleSupportingBasis targeted () true true ∧
    WarrantNeedsUndefeatedSupport targeted () true ∧
    LacksTargetWarrant targeted () true ∧ targeted.holds true ∧
    ThereAreEpistemicReasons (UndefeatedSupport targeted)) ∧
  (AcceptedPackage supported () true ∧
    PackageRaisesReliabilityConcern supported () true true ∧
    ReliabilityConcernUndercuts supported () true ∧
    BasisUndercut supported () true ∧ ¬ SoleSupportingBasis supported () true true ∧
    WarrantNeedsUndefeatedSupport supported () true ∧ supported.warranted () true) ∧
  (AcceptedPackage noConcern () true ∧
    ¬ PackageRaisesReliabilityConcern noConcern () true true ∧
    ReliabilityConcernUndercuts noConcern () true ∧
    SoleSupportingBasis noConcern () true true ∧
    WarrantNeedsUndefeatedSupport noConcern () true ∧ noConcern.warranted () true) ∧
  (AcceptedPackage policyRejected () true ∧
    PackageRaisesReliabilityConcern policyRejected () true true ∧
    ¬ ReliabilityConcernUndercuts policyRejected () true ∧
    SoleSupportingBasis policyRejected () true true ∧
    WarrantNeedsUndefeatedSupport policyRejected () true ∧ policyRejected.warranted () true)

end TruthCore.Logic.GlobalThesisBoundaries
