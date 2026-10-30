import TruthCore.Logic.Relativism
import TruthCore.Logic.TruthPilot

/-!
Nontriviality of truth (#556): what a global collapse or denial of truth can
and cannot coherently assert.

Three levels are kept apart. `GlobalPropositionalCollapse` is about Lean's
`Prop`. `Collapse` is about one truth predicate on a content type, which is a
parameter, so a theorem about it says nothing about a rival until the rival's
predicate is supplied. In these laws a collapse of a predicate reaches Lean's
`Prop` only through `Expressive`, a bridge a rival may deny.

Everything here is about an encoded logic and stipulated test semantics. Nothing
says what relativists or nihilists hold; nothing here is about mind-independent
truth, and `Prop` has no world parameter. No statement is attributed to a source.
-/

namespace TruthCore.Logic.TruthNontriviality

open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
open TruthCore.Logic.TruthPilot

/-- All Lean propositions are pairwise equivalent. `↔`, not `=`, so no `propext`. -/
def GlobalPropositionalCollapse : Prop := ∀ P Q : Prop, P ↔ Q

/-- Not all Lean propositions are pairwise equivalent
(`STMT-NO-GLOBAL-PROPOSITIONAL-COLLAPSE`). -/
def NoGlobalPropositionalCollapse : Prop := ¬ GlobalPropositionalCollapse

variable {Content : Type}

/-- A truth predicate does not distinguish any two contents. -/
def Collapse (truth : Content → Prop) : Prop := ∀ p q, truth p ↔ truth q

/-- Every content satisfies the predicate. -/
def AllHold (truth : Content → Prop) : Prop := ∀ p, truth p

/-- No content satisfies the predicate. -/
def AllFail (truth : Content → Prop) : Prop := ∀ p, ¬ truth p

/-- For every Lean proposition some content's truth is equivalent to it. The
bridge from a predicate to `Prop`; a stipulated condition, not a claim that any
natural language or rival's language has it. -/
def Expressive (truth : Content → Prop) : Prop := ∀ P : Prop, ∃ c, truth c ↔ P

/-- Each content or its expressed negation is true. The partner of
`TruthCore.Logic.TruthPilot.NegationRespected`, which is exclusion. -/
def NegationExhaustive (truth : Content → Prop) (neg : Content → Content) : Prop :=
  ∀ p, truth p ∨ truth (neg p)

/-- The capture half of the truth schema for a no-absolute-truth thesis: if no
content is absolutely true, the thesis content is absolutely true. The other
half is `ThesisDisquotes`. -/
def CapturesThesis {Agent : Type} (T : TruthSemantics Agent Content) (thesis : Content) : Prop :=
  GlobalNoAbsoluteTruth T → T.trueAbs thesis

/-- No content is true in any sense this semantics has: not absolutely, and not
for any agent. -/
def GlobalTruthNihilism {Agent : Type} (T : TruthSemantics Agent Content) : Prop :=
  GlobalNoAbsoluteTruth T ∧ ∀ a p, ¬ T.trueFor a p

/-- Laws of predicate collapse for every content type, predicate and negation
operator. The first law is the only one reaching `Prop`. The second and third
say that the two poles collapse; the fourth is the fork (coverage needs a
decided pivot) and the fifth its exclusivity on inhabited contents. The last
three factor negation: exclusion forces the failing pole, exhaustion the holding
pole, and both are incompatible with collapse on inhabited contents. -/
def CollapseLaws : Prop :=
  ∀ (Content : Type) (truth : Content → Prop) (neg : Content → Content),
    (Expressive truth → ¬ Collapse truth) ∧
    (AllHold truth → Collapse truth) ∧
    (AllFail truth → Collapse truth) ∧
    (∀ p₀, Collapse truth → (truth p₀ ∨ ¬ truth p₀) → AllHold truth ∨ AllFail truth) ∧
    (∀ _p₀ : Content, AllHold truth → AllFail truth → False) ∧
    (Collapse truth → NegationRespected truth neg → AllFail truth) ∧
    (Collapse truth → NegationExhaustive truth neg → AllHold truth) ∧
    (∀ _p₀ : Content,
      Collapse truth → NegationRespected truth neg → NegationExhaustive truth neg → False)

/-- What a global denial costs, for every semantics. That no content is absolutely
true entails that the absolute predicate collapses and is not expressive and, on
inhabited contents, that negation is not exhaustive for it. A thesis that
disquotes and captures entails that the global denial fails. Total nihilism
entails that no assertion commitment in any truth sense is met and that no
agent's predicate is expressive. -/
def GlobalDenialPrice : Prop :=
  ∀ (Agent Content : Type) (T : TruthSemantics Agent Content),
    (GlobalNoAbsoluteTruth T → Collapse T.trueAbs ∧ ¬ Expressive T.trueAbs) ∧
    (∀ (neg : Content → Content) (_p₀ : Content),
      GlobalNoAbsoluteTruth T → ¬ NegationExhaustive T.trueAbs neg) ∧
    (∀ thesis, ThesisDisquotes T (fun _ => True) thesis → CapturesThesis T thesis →
      ¬ GlobalNoAbsoluteTruth T) ∧
    (GlobalTruthNihilism T → ∀ s p, ¬ AssertionCommitment T s p) ∧
    (∀ a, Expressive (T.trueFor a) → ¬ GlobalTruthNihilism T)

/-- The laws and the price (`STMT-TRUTH-NONTRIVIALITY-CORE`). -/
def TruthNontrivialityCore : Prop := CollapseLaws ∧ GlobalDenialPrice

/-- Local collapse survives: an expressive, uncollapsed predicate with one
two-member domain where all hold and another where all fail. -/
def LocalCollapseModel : Prop :=
  ∃ (Content : Type) (truth : Content → Prop) (Dh Df : Norm.Demarcation Content),
    Expressive truth ∧ ¬ Collapse truth ∧
    (∃ p q, p ≠ q ∧ Dh.inDomain p ∧ Dh.inDomain q) ∧
    (∀ p, Dh.inDomain p → truth p) ∧
    (∃ p q, p ≠ q ∧ Df.inDomain p ∧ Df.inDomain q) ∧
    (∀ p, Df.inDomain p → ¬ truth p)

/-- Profile-indexed truth survives on the pilot language: global variation with
every profile's predicate collapsed; global variation with some profile's
predicate uncollapsed; and the pilot's logical-stable local variation. -/
def ProfileVariationModels : Prop :=
  (∃ Holds : Interpretation, GlobalProfileVariation Holds ∧ ∀ E, Collapse (Holds E)) ∧
  (∃ Holds : Interpretation, GlobalProfileVariation Holds ∧ ∃ E, ¬ Collapse (Holds E)) ∧
  LogicalTruthsCompatibleWithVariation

/-- The propositional floor is compatible with a one-point type: an inhabited type
with no two distinct elements, a step function fixing each element, and an empty
binary relation. The type, function and relation are uninterpreted; this is not
a model of a world, of change or of causes, and shows only that the floor does
not constrain them, since `NoGlobalPropositionalCollapse` has no such parameter. -/
def UndifferentiatedStructureModel : Prop :=
  NoGlobalPropositionalCollapse ∧
    ∃ (W : Type) (step : W → W) (R : W → W → Prop),
      Nonempty W ∧ (∀ x y : W, x = y) ∧ (∀ x, step x = x) ∧ ∀ x y, ¬ R x y

/-- A predicate-and-negation pair, in Lean's own metatheory, where some content
and its expressed negation both hold and another content fails: truth-preservation
from `p, neg p` to `q` fails. Negation is exhaustive and not exclusive, and the
predicate does not collapse. A stipulated structure, not a dialetheist's own
semantics; `NoGlobalPropositionalCollapse` does not test such a change of profile. -/
def GlutModel : Prop :=
  ∃ (Content : Type) (truth : Content → Prop) (neg : Content → Content),
    (∃ p, truth p ∧ truth (neg p)) ∧ (∃ q, ¬ truth q) ∧
    NegationExhaustive truth neg ∧ ¬ NegationRespected truth neg ∧ ¬ Collapse truth

/-- Both collapse poles are realized on inhabited contents, so neither half of
negation is redundant: all-hold with exhaustive, non-exclusive negation; all-fail
with exclusive, non-exhaustive negation. -/
def CollapseHornModels : Prop :=
  (∃ (Content : Type) (truth : Content → Prop) (neg : Content → Content),
    Nonempty Content ∧ AllHold truth ∧ NegationExhaustive truth neg ∧
      ¬ NegationRespected truth neg) ∧
  (∃ (Content : Type) (truth : Content → Prop) (neg : Content → Content),
    Nonempty Content ∧ AllFail truth ∧ NegationRespected truth neg ∧
      ¬ NegationExhaustive truth neg)

/-- The relativist survivor: no content is absolutely true, the thesis disquotes
and does not capture, every agent's predicate is expressive and uncollapsed, and
a relative assertion of the thesis is met for one agent and not the other.
Adds expressive relative truth to the conditions of `RelativeHornConsistent`,
whose statement fixes `Bool` contents and does not ask for it. Consistency only. -/
def RelativeSurvivorModel : Prop :=
  ∃ (Content : Type) (T : TruthSemantics Bool Content) (thesis : Content) (a : Bool),
    GlobalNoAbsoluteTruth T ∧ ThesisDisquotes T (fun _ => True) thesis ∧
    ¬ CapturesThesis T thesis ∧
    (∀ b, Expressive (T.trueFor b)) ∧ (∀ b, ¬ Collapse (T.trueFor b)) ∧
    AssertionCommitment T (TruthSense.relativeTo a) thesis ∧ ¬ T.trueFor (!a) thesis

/-- Total nihilism is consistent on inhabited contents, with exclusive negation.
Consistency only; `GlobalDenialPrice` gives what it then cannot meet. -/
def TotalNihilistModel : Prop :=
  ∃ (Content : Type) (T : TruthSemantics Bool Content) (neg : Content → Content),
    Nonempty Content ∧ GlobalTruthNihilism T ∧ NegationRespected T.trueAbs neg

/-- Disquotation with capture is satisfiable: the thesis is not absolutely true
and another content is. So those two hypotheses of `GlobalDenialPrice` are
jointly satisfiable, without a contradiction. -/
def ThesisSchemaModel : Prop :=
  ∃ (Content : Type) (T : TruthSemantics Bool Content) (thesis other : Content),
    ThesisDisquotes T (fun _ => True) thesis ∧ CapturesThesis T thesis ∧
    ¬ T.trueAbs thesis ∧ T.trueAbs other

/-- The anti-overclaim controls (`STMT-TRUTH-COLLAPSE-CONTROLS`). Each conjunct is
the existence of a model, not a defense of what it models. -/
def TruthCollapseControls : Prop :=
  LocalCollapseModel ∧ ProfileVariationModels ∧ UndifferentiatedStructureModel ∧
    GlutModel ∧ CollapseHornModels ∧ RelativeSurvivorModel ∧ TotalNihilistModel ∧
    ThesisSchemaModel

end TruthCore.Logic.TruthNontriviality
