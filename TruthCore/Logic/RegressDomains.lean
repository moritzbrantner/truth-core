import TruthCore.Logic.Regress
import TruthCore.Logic.SelfApplication
import TruthCore.Greek.Plato.ParticipationGrounding
import TruthCore.Explanation.ExistencePSR
import TruthCore.Results.Case.Catholicism.CausalFinitism.Solution
import TruthCore.Results.Causality.GroundingYieldsRegress.Solution
import TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress.Solution

/-!
Six distinct domain adapters for #412. These are analyst conditionals, not
historical attributions or assertions of actual well-foundedness. Efficient
causes and movers reuse their existing, different relations; grounding uses
fact tokens, explanation reason/existence-fact tokens, parthood strict order,
and justification claim tokens. No cross-domain truth bridge is automatic.
-/
namespace TruthCore.Logic.RegressDomains
open TruthCore.Logic.Regress TruthCore.Causality
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Case.Catholicism.StageOne.CausalFinitism

/-- Efficient-cause graph, preserving the existing per se edge's orientation. -/
def efficient {Being : Type} (CausesAsCaused : Being → Being → Prop) : Graph Being :=
  ⟨CausesAsCaused⟩

/-- Typed physical mover graph; moved-by-another includes its existing
nonidentity and respect witnesses and is not ordinary efficient causation. -/
def motion {Being Respect : Type} (MovesIn : Being → Being → Respect → Prop) : Graph Being :=
  ⟨MoverMovedByAnotherLink MovesIn⟩

/-- Ground-to-grounded fact edges, not logical implication or warrant. -/
def grounding {E Q F : Type}
    (e : TruthCore.Greek.Plato.ParticipationGrounding.Explanation E Q F) :
    Graph (TruthCore.Greek.Plato.ParticipationGrounding.Fact E Q F) := ⟨e.Grounds⟩

/-- Existence-PSR reasons have a different type from their explananda.
`requires` separately records which existence facts a reason presupposes.
The projected edge p→q means an admitted reason for q requires p. Neither
PSR nor its soundness condition supplies this new dependency datum. -/
structure ExplanatoryDependence (World Being : Type) where
  model : TruthCore.Explanation.ExistencePSR.Model World Being
  requires : TruthCore.Explanation.ExistencePSR.Reason Being →
    TruthCore.Explanation.ExistencePSR.ExistenceFact Being → Prop

def explanation {W B : Type} (e : ExplanatoryDependence W B) (w : W) :
    Graph (TruthCore.Explanation.ExistencePSR.ExistenceFact B) :=
  ⟨fun p q => ∃ r, e.model.explains w r q ∧ e.requires r p⟩

/-- Strict parthood in a supplied partial order. The order's interpretation
as parthood is stipulative; no fusion, supplementation or atomism is assumed. -/
def parthood (Part : Type) [PartialOrder Part] : Graph Part := ⟨(· < ·)⟩

/-- Inferential dependence, noninferential foundation, and epistemic
justification are different fields. The latter is not defined as a path.
GeneratedWarrant below is one explicitly foundationalist inferential standard,
not an attributed account of all possible justification. -/
structure Justification (Claim : Type) where
  Rule : Type
  premise : Rule → Claim → Prop
  conclusion : Rule → Claim
  noninferential : Claim → Prop
  justified : Claim → Prop

/-- An inference edge remembers membership in an entire rule's premise set.
It does not assert that this single premise suffices for its conclusion. -/
def Justification.inferential {C : Type} (j : Justification C) (p c : C) : Prop :=
  ∃ r, j.conclusion r = c ∧ j.premise r p

def justificatory {C : Type} (j : Justification C) : Graph C := ⟨j.inferential⟩
/-- All premises of one rule must themselves carry generated warrant. Empty
rules are permitted as data; the path-to-foundation transfer below explicitly
requires nonempty inferential rules. No rule is silently reduced to one edge. -/
inductive GeneratedWarrant {C : Type} (j : Justification C) : C → Prop where
  | foundation (c) : j.noninferential c → GeneratedWarrant j c
  | inference (r : j.Rule) : (∀ p, j.premise r p → GeneratedWarrant j p) →
      GeneratedWarrant j (j.conclusion r)


/-- Finite ancestry, no finite causal loops, and same-carrier inclusion imply
schema controls for per se efficient causes. Uses the #433 route, not a new
identification of finitism with accessibility. -/
def EfficientTransfer : Prop :=
  ∀ (B : Type) (cause perSe : B → B → Prop),
    FiniteDistinctAncestry cause → NoCausalLoops cause → PerSeLinksIncluded cause perSe →
      (efficient perSe).Controls

/-- The III.3 and second-mover bridges transfer the First Way's stronger
accessibility commitment to the typed physical relation. The weaker source
prohibition of infinitely many distinct movers is not strengthened here. -/
def MotionTransfer : Prop :=
  ∀ (B R : Type) (MovedIn : B → R → Prop) (MovesIn : B → B → R → Prop)
    (MovesAsMoved : B → B → Prop),
    MovingIsInTheMovedReading MovesIn MovedIn →
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved → (motion MovesIn).Controls

/-- Existing finite-source grounding plus sources without incoming links and unique
immediate predecessors gives accessibility of the separately typed Grounds
relation. No principle of real metaphysical ground is asserted. -/
def GroundingTransfer : Prop :=
  ∀ (E Q F : Type) (e : TruthCore.Greek.Plato.ParticipationGrounding.Explanation E Q F)
    (intrinsic : TruthCore.Greek.Plato.ParticipationGrounding.Fact E Q F → Prop),
    (∀ p, FinitelyGroundedPower e.Grounds intrinsic p) →
      GroundingRegress.SourcesReceiveNoLink e.Grounds intrinsic →
      GroundingRegress.AtMostOneImmediateCause e.Grounds → (grounding e).Controls

/-- An independently supplied well-founded rank of existence facts controls
explanation regress only when every admitted reason's required fact lies
strictly below its explanandum. PSR alone supplies no such rank. -/
def ExplanationTransfer : Prop :=
  ∀ (W B Rank : Type) (e : ExplanatoryDependence W B) (w : W)
    (lower : Rank → Rank → Prop)
    (rank : TruthCore.Explanation.ExistencePSR.ExistenceFact B → Rank),
    WellFounded lower →
      (∀ r p q, e.model.explains w r q → e.requires r p → lower (rank p) (rank q)) →
        (explanation e w).Controls

/-- Well-founded strict parthood gives an atom below each object. Relative
sources here are atoms, not intrinsic causal powers or noninferential beliefs. -/
def ParthoodTransfer : Prop :=
  ∀ (P : Type) (ord : PartialOrder P),
    WellFounded (fun a b : P => @LT.lt P ord.toLT a b) →
      (parthood P).Controls

/-- Each generated warrant has a finite inferential path to a stipulated
noninferential foundation; this is weaker than well-foundedness of every
inferential edge and does not assert epistemic justification. -/
def JustificationTransfer : Prop :=
  ∀ (C : Type) (j : Justification C) (c : C),
    (∀ r, ∃ p, j.premise r p) → GeneratedWarrant j c →
    ∃ foundation, FiniteCausalPath j.inferential c foundation ∧ j.noninferential foundation

/-- Minimal structural transfer used here: an explicit causal-to-justificatory
edge-preserving map and well-foundedness of the epistemic relation. These are
open bridge hypotheses, not consequences of rejecting an unwarranted belief.
The conclusion is only relative to the supplied causal relation. -/
def EpistemicBridge : Prop :=
  ∀ (B C : Type) (causal : Graph B) (j : Justification C)
    (_bridge : causal.Map (justificatory j)),
    WellFounded j.inferential → causal.Controls

/-- Discrimination on the very same infinite graph: a local all-on causal
assignment (gfp) exists, while the finite-foundation warrant interpretation
(lfp) warrants nothing. All beings are stipulated existent, all epistemic
justification is withheld. This is satisfiability of the encoding, not actual
physical possibility; temporal causation and per se power remain distinct. -/
def CrossDomainBoundary : Prop :=
  ∃ (causal : Graph Nat) (j : Justification Nat) (existsOntically active : Nat → Prop),
    (∀ y x, causal.edge y x ↔ j.inferential y x) ∧
    (∀ x, existsOntically x ∧ active x ∧ ¬ j.justified x ∧ ¬ GeneratedWarrant j x) ∧
    (∀ x, ¬ causal.Source x) ∧
    PowerTransmissionRule causal.edge active ∧
    0 ∈ (causal.transmission (fun _ => False)).gfp ∧
    0 ∉ (causal.transmission (fun _ => False)).lfp ∧
    ¬ WellFounded causal.edge

/-- Finite one-node cycles are rejected by accessibility even though their
unrolling has no infinitely many distinct nodes. Fixed-point equality alone
is also weaker than well-foundedness: supplying every node intrinsically
makes both fixed points total even on a self-loop. -/
def CycleAndConverseBoundary : Prop :=
  ∃ G : Graph Unit,
    ¬ WellFounded G.edge ∧
    (¬ ∃ s : Nat → Unit, Function.Injective s) ∧
    (G.transmission (fun _ => True)).lfp = (G.transmission (fun _ => True)).gfp

/-- Self-application of a philosopher's own norm to a positive knowledge claim
about causal possibility. Scope and failure of the stated epistemic standard
remain explicit. Mere suspension is not positive knowledge or a modal proof. -/
def KnowledgeSelfApplication : Prop :=
  ∀ (C : Type) (j : Justification C) (knows : C → Prop)
    (norm : TruthCore.Logic.SelfApplication.Norm C) (possibilityClaim : C),
    (∀ c, norm.standard c ↔ j.justified c) →
      norm.scope possibilityClaim → ¬ j.justified possibilityClaim →
        (norm.Holds knows → ¬ knows possibilityClaim) ∧
        (knows possibilityClaim → norm.Counterexample knows possibilityClaim)

/-- Strict parthood can be atomless without cycles: reversed natural-number
order gives every whole a proper part. This rejects well-founded parts-priority,
not the consistency of a mereological order or whole-priority. -/
def AtomlessBoundary : Prop :=
  (∀ x : OrderDual Nat, ∃ y, (parthood (OrderDual Nat)).edge y x) ∧
    (∀ x : OrderDual Nat, ¬ (parthood (OrderDual Nat)).edge x x) ∧
    (∀ x y z : OrderDual Nat, (parthood (OrderDual Nat)).edge x y →
      (parthood (OrderDual Nat)).edge y z → (parthood (OrderDual Nat)).edge x z) ∧
    ¬ WellFounded (parthood (OrderDual Nat)).edge

/-- A finite branch to a foundation is insufficient for warrant when another
premise of the same rule remains unsupported. This tests the all-premise
semantics against the tempting unary-path replacement. -/
def AllPremiseBoundary : Prop :=
  ∃ j : Justification Bool,
    (∀ r, ∃ p, j.premise r p) ∧
    FiniteCausalPath j.inferential false true ∧ j.noninferential true ∧
    ¬ GeneratedWarrant j false

/-- A weaker, semantic bridge sufficient only for excluding globally
source-free active systems: actual activity must meet this warrant standard,
and any noninferential foundation must imply some source in the causal graph.
Both links are explicit open conditions, independently of graph isomorphism.
No conclusion about merely temporal succession follows. -/
def SourceFreeSemanticBridge : Prop :=
  ∀ (B C : Type) (causal : Graph B) (j : Justification C)
    (active : B → Prop) (claimOf : B → C),
    (∀ r, ∃ p, j.premise r p) →
    (∀ x, active x → GeneratedWarrant j (claimOf x)) →
    (∀ p, j.noninferential p → ∃ s, causal.Source s) →
    (∀ s, ¬ causal.Source s) → ∀ x, ¬ active x

/-- All discriminating controls, plus the explicitly hypothetical bridge and
self-application test. No actual epistemic or causal standard is established. -/
def BoundaryControls : Prop :=
  EpistemicBridge ∧ CrossDomainBoundary ∧ CycleAndConverseBoundary ∧
    KnowledgeSelfApplication ∧ AtomlessBoundary ∧ AllPremiseBoundary ∧ SourceFreeSemanticBridge

/-- The full package certifies six separate transfers, the conditional bridge,
and discriminating controls. It discharges no actual philosophical premise. -/
def DomainPackage : Prop :=
  StructuralSchema ∧ EfficientTransfer ∧ MotionTransfer ∧ GroundingTransfer ∧ ExplanationTransfer ∧
    ParthoodTransfer ∧ JustificationTransfer ∧ BoundaryControls

end TruthCore.Logic.RegressDomains
