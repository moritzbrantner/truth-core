import TruthCore.Results.Metaethics.PlanStateEmbeddingControl.Solution

/-!
A stipulative test prompted by Carneades's reasons objection (research notes in
`docs/notes/carneades-metaethics-reasons.md`). No historical claim is bound here.
We reuse the existing material support semantics, not Gibbard's indicative
semantics. Factual information can guide a plan conditional on a normative
commitment, while a satisfiable purely factual theory leaves all actions
permitted in some compatible point. Neither property settles categorical
normative warrant, ordinary-language adequacy, or substantive moral realism.
-/
namespace TruthCore.Metaethics.DescriptivePlanBoundary
open TruthCore.Metaethics.PlanStateEmbedding

/-- Syntactically factual fragment of the existing planning language. This
excludes every forbidden-action occurrence, including embedded ones. It is a
stipulative syntactic restriction, not a criterion for natural-language facts. -/
def Descriptive {Fact Action : Type} : Sentence Fact Action → Prop
  | .factual _ => True
  | .forbidden _ => False
  | .conditional p q => Descriptive p ∧ Descriptive q

/-- Every satisfiable theory entirely in the factual fragment has a compatible
point permitting every action. Thus it cannot semantically force exclusion of
any action. The satisfiability condition excludes explosion from inconsistent
premises. Arbitrarily many factual premises and nested conditionals are allowed. -/
def FactualFreedom : Prop :=
  ∀ (Fact Action : Type) (theory : Set (Sentence Fact Action)),
    (∀ p ∈ theory, Descriptive p) →
    (∃ w, ∀ p ∈ theory, w ∈ support p) →
    ∃ w, (∀ p ∈ theory, w ∈ support p) ∧ ∀ a, w.permitted a = true

/-- Plan-conditioned responsiveness: factual acceptance and an accepted
factual-to-forbidden conditional entail acceptance of that prohibition.
The conditional is an explicit normative commitment, not a fact-only premise. -/
def ConditionalGuidance : Prop :=
  ∀ (Fact Action : Type) (state : Set (Point Fact Action)) (f : Fact) (a : Action),
    Accepts state (.factual f) →
    Accepts state (.conditional (.factual f) (.forbidden a)) →
    Accepts state (.forbidden a)

/-- The normative bridge is not redundant: a nonempty singleton state accepts
the factual atom but rejects its proposed forbidden consequence and conditional.
An alternative action is available in every point, preventing no-option vacuity. -/
def BridgeOmission : Prop :=
  ∃ state : Set (Point Unit ExampleAction), state.Nonempty ∧
    (∀ w ∈ state, w.permitted .abstain = true) ∧
    Accepts state (.factual ()) ∧
    ¬ Accepts state (.forbidden .direct) ∧
    ¬ Accepts state (.conditional (.factual ()) (.forbidden .direct))

/-- Joint boundary, not a theory verdict: factual freedom, conditional guidance,
and a nonempty omission control under the existing material support clauses. -/
def Boundary : Prop := FactualFreedom ∧ ConditionalGuidance ∧ BridgeOmission

/-- Descriptive support is invariant under changing only the permission plan.
This structural fact, rather than a primitive is/ought axiom, drives the result. -/
theorem descriptiveSupport {Fact Action : Type} (p : Sentence Fact Action)
    (hp : Descriptive p) (w v : Point Fact Action) (h : w.factual = v.factual) :
    w ∈ support p ↔ v ∈ support p := by
  induction p with
  | factual f => change w.factual f = true ↔ v.factual f = true; rw [h]
  | forbidden a => exact False.elim hp
  | conditional p q ihp ihq =>
    change (w ∉ support p ∨ w ∈ support q) ↔ (v ∉ support p ∨ v ∈ support q)
    exact or_congr (not_congr (ihp hp.1)) (ihq hp.2)
end TruthCore.Metaethics.DescriptivePlanBoundary
