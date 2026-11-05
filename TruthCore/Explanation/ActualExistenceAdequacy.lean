module

public import TruthCore.Explanation.ExplanatoryAdequacy
public import TruthCore.Causality.BruteFoundationBoundary
public import TruthCore.Modern.Hume.Regularity

/-!
# #750: independent verification and intervention on one concrete bearer

Analyst finite specialization, NOT the full first-order Hempel–Oppenheim theory.
Logical valuations, accessible worlds and intervention contexts are three
explicitly different domains. Hempel–Oppenheim (1948), pp.160–164, §§7.5–7.8,
motivate basic-sentence verification independence but reject banning all shared
content. Woodward, Human Face, pp.71–76, requires admissible interventions,
not mere observation; pp.90–93 leave global extension open. Neither source
establishes that the tables below apply to ultimate existential explanation.
-/

@[expose] public section
namespace TruthCore.Explanation.ActualExistenceAdequacy
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Modern.Hume.Regularity

/-- Facts, not beings: a proposed condition and this bearer's existence. -/
inductive Atom | reason | target deriving DecidableEq

/-- Logically unrestricted assignments, not accessible metaphysical worlds. -/
abbrev Valuation := Bool × Bool

def eval (v : Valuation) : Atom → Prop
  | .reason => v.1 = true
  | .target => v.2 = true

/-- A basic sentence or its denial, as in H–O p.163. -/
abbrev Literal := Atom × Bool

def verified (v : Valuation) (evidence : List Literal) : Prop :=
  ∀ l ∈ evidence, if l.2 then eval v l.1 else ¬ eval v l.1

/-- Finite propositional specialization of H–O §7.8(3), strengthened to
actually true evidence for an actual account. The law is compatible with a
basic class entailing the condition but not the target. Compatibility does NOT
require a law-world where the condition holds and the target fails. No
lawlikeness, empirical testability or first-order generality is certified. -/
def VerificationIndependent (condition : Valuation → Prop) : Prop :=
  ∃ evidence : List Literal,
    verified (true, true) evidence ∧
    (∀ v, verified v evidence → condition v) ∧
    ¬ (∀ v, verified v evidence → eval v .target) ∧
    ∃ v, verified v evidence ∧ (eval v .reason ↔ eval v .target)

/-- The SAME bearer `()` and existence fact in every response-table account.
Worlds are complete alternatives indexed by the experiment's backgrounds;
identifying these with metaphysically possible worlds is an OPEN application
bridge. No causal claim is inferred: the Ontic cause field is empty. -/
def arena (m : Experiment) : Arena Bool Unit Atom where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => m.y w = true
    Causes := fun _ _ _ => False }
  holds := fun w f => match f with
    | .reason => m.x w = true
    | .target => m.y w = true
  exist := fun _ => .target
  explains := fun w r f => r = .reason ∧ f = .target ∧ m.x w = true ∧ m.y w = true
  conjunct := fun f g => f = g

/-- Concrete kind is explicit framework data; it is not inferred from an
unconstrained Fact label. This reuses the existing Ontic/Profile vocabulary.
Grounding is empty, so no existential support is smuggled into the input. -/
def profile (m : Experiment) : Profile Bool Unit :=
  ⟨(arena m).ontic, fun _ => True, fun _ _ _ => False⟩

/-- Both models really carry coherent existence, actuality, concreteness and
contingency of the rigid bearer `()`. They are mathematical models, not evidence
that an actual worldly individual has been empirically identified. -/
def Target (m : Experiment) : Prop :=
  Coherent (arena m) ∧ (profile m).concrete () ∧
    (arena m).ontic.ExistsAt true () ∧
    ContingentAt (arena m).ontic true () ∧
    Contingent (arena m) true ((arena m).exist ())

/-- Intervention relevance is the EXISTING Changes predicate on the supplied
response table. Whether settings are admissible under Woodward's IV is OPEN;
this criterion is conditional on that interpretation, not a reduction.
Response pairs are not Arena worlds: realizing them as the same bearer's
ExistsAt is a separate OPEN bridge. -/
def InterventionRelevant (m : Experiment) : Prop := Changes m.setX

/-- This certificate does not select an ontology or close #750. -/
def Comparison : Prop :=
  Target chain ∧ Target fork ∧
  (∀ w b, (arena chain).ontic.ExistsAt w b ↔ (arena fork).ontic.ExistsAt w b) ∧
  (∀ w f, (arena chain).holds w f ↔ (arena fork).holds w f) ∧
  VerificationIndependent (fun v => eval v .reason) ∧
  ¬ VerificationIndependent (fun v => eval v .target) ∧
  (∀ w, (arena chain).holds w .reason ↔ (arena chain).holds w .target) ∧
  InterventionRelevant chain ∧ ¬ InterventionRelevant fork
end TruthCore.Explanation.ActualExistenceAdequacy

@[expose] public section
namespace TruthCore.Explanation.ActualExistenceAdequacy
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Modern.Hume.Regularity

/-- Observations and ideal settings are tagged separately. Interpreting all of
these as accessible metaphysical possibilities is an explicit model commitment,
not a source-derived fact. -/
abbrev ResponseWorld := Sum Bool (Bool × Bool)

def responseY (m : Experiment) : ResponseWorld → Bool
  | .inl w => m.y w
  | .inr (u, setting) => m.setX u setting

def responseX (m : Experiment) : ResponseWorld → Bool
  | .inl w => m.x w
  | .inr (_, setting) => setting

/-- Conditional realization: every response output IS the same bearer's existence
at its tagged setting world. This constructs a consistent interpretation; it
does not establish IV admissibility or real-world existential production. -/
def realized (m : Experiment) : Arena ResponseWorld Unit Atom where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w _ => responseY m w = true
    Causes := fun _ _ _ => False }
  holds := fun w f => match f with
    | .reason => responseX m w = true
    | .target => responseY m w = true
  exist := fun _ => .target
  explains := fun w r f => r = .reason ∧ f = .target ∧
    responseX m w = true ∧ responseY m w = true
  conjunct := fun f g => f = g

def realizedProfile (m : Experiment) : Profile ResponseWorld Unit :=
  ⟨(realized m).ontic, fun _ => True, fun _ _ _ => False⟩

def RealizedTarget (m : Experiment) : Prop :=
  Coherent (realized m) ∧ (realizedProfile m).concrete () ∧
  (realized m).ontic.ExistsAt (.inl true) () ∧
  ContingentAt (realized m).ontic (.inl true) () ∧
  Contingent (realized m) (.inl true) ((realized m).exist ())

/-- A genuine difference in the interpreted EXISTENCE of the same bearer at
setting worlds; source fidelity/admissibility/application remain separate. -/
def ExistentialResponse (m : Experiment) : Prop :=
  ∃ u, ¬ ((realized m).ontic.ExistsAt (.inr (u, false)) () ↔
    (realized m).ontic.ExistsAt (.inr (u, true)) ())

/-- Identical observational reduct, NOT identical full world profiles. -/
def RealizationComparison : Prop :=
  RealizedTarget chain ∧ RealizedTarget fork ∧
  (∀ m w b, (realized m).ontic.ExistsAt (.inl w) b ↔ (arena m).ontic.ExistsAt w b) ∧
  (∀ w f, (realized chain).holds (.inl w) f ↔ (realized fork).holds (.inl w) f) ∧
  (∀ m u setting, (realized m).ontic.ExistsAt (.inr (u, setting)) () ↔
    m.setX u setting = true) ∧
  ExistentialResponse chain ∧ ¬ ExistentialResponse fork ∧
  ¬ ((realized chain).ontic.ExistsAt (.inr (true, false)) () ↔
    (realized fork).ontic.ExistsAt (.inr (true, false)) ()) ∧
  VerificationIndependent (fun v => eval v .reason)
end TruthCore.Explanation.ActualExistenceAdequacy
