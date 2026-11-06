# Shared belief closure under two logics (#1084 / #932)

This analyst test isolates one additional bridge in the normativity/collapse
discussion: require **one and the same selected belief pool** to be closed under
both consequence relations. It proves a new joint consequence and each omitted
input's control. It neither proves that this policy is obligatory nor that two
logics have the same validities. Attribution is deferred.

## Reuse inventory and semantic boundary

The related/dossier inventory inspected `STMT-REFLECTIVE-COHERENCE-BOUNDARY`,
`STMT-TRANSCENDENTAL-AGENCY-DUTY-BOUNDARY` and the existing intuitionistic
knowability survivor. `SelfApplication`, `AssertionCommitment`, `KnowledgeRetorsion`
and `PerformedDenial` already separate accepted norms, assertion/performance,
accuracy and factivity. Their retorsions are not repeated.

`ReflectiveCoherence.Semantics` and `Verificationism.Language` require object
negation to coincide with Lean negation at every world. They cannot faithfully
represent the gaps and gluts used here. `IntuitionisticKnowability.Content`
provides actual Mathlib Heyting semantics, not these matrices. No suitable shared
K3/LP/FDE syntax/valuation or semantic belief-closure implementation was found.
A nested classical/Heyting closure comparison was rejected as too close to a
generic inclusion lemma. ThresholdBelief concerns probability-to-full-belief and
conjunction closure, and Fitch concerns knowledge/knowability; neither compares
two incomparable consequence relations on shared syntax.

The new local language has exactly two atoms, with negation, conjunction and
disjunction. Values are **one shared pair of Boolean truth/falsity bits**:

| Label | Truth bit | Falsity bit |
|---|---|---|
| T | true | false |
| F | false | true |
| Neither | false | false |
| Both | true | true |

Negation swaps bits. Conjunction ANDs truth and ORs falsity; disjunction ORs
truth and ANDs falsity. Designation means the truth bit is true. K3 admits
atomic valuations without Both; LP admits atomic valuations without Neither.
There is no change of connective tables between the two. Object-language Both
is not an instance of `P ∧ ¬P` in Lean. Neither accepted F1 nor F6 changes.

`Consequence L Γ a` quantifies over every admitted valuation and requires
preservation of designation from all finite listed premises to the conclusion.
`Closed L B` requires this for all finite lists whose members are in pool B.
Pools are extensional selected sets, not actual psychological belief states,
permission predicates, pro tanto reasons or categorical obligations.

## Joint consequence absent from both individual relations

Write:

- `g = p ∨ (q ∧ ¬q)`;
- `e = q ∨ ¬q`;
- `C = p ∧ e`.

K3 validates **g ⊢ p**, since `q ∧ ¬q` cannot be designated under its admitted
valuations. LP validates **∅ ⊢ e**. Conjunction introduction is valid in both.
Thus for every pool B:

`B(g) ∧ Closed K3 B ∧ Closed LP B → B(C)`.

No object-language conditional is used: the turnstile denotes the defined
semantic consequence relation, and the displayed implication concerns the
policy. The proof actually composes the three semantic moves, rather than
assuming a bridge whose conclusion already is B(C).

Neither individual relation validates **g ⊢ C**:

| Profile | p | q | g | C |
|---|---|---|---|---|
| K3 countervaluation | T | Neither | T | Neither |
| LP countervaluation | F | Both | Both | F |

These also witness incomparability: the LP valuation defeats g ⊢ p, and the K3
valuation defeats the empty-premise e theorem. Both relations use all finite
formulas in the fixed two-atom signature, not unrelated bare rule flags.

## Deletions and survivors are closed theories

The frozen joint certificate carries the semantic distinctions, the conditional
shared-closure law, all three deletions and the surviving shared/indexed pools:

- Delete LP closure: the K3 semantic theory of g contains g, is K3-closed,
  rejects C and is not LP-closed.
- Delete K3 closure: the LP semantic theory of g contains g, is LP-closed,
  rejects C and is not K3-closed.
- Delete initial acceptance: the designated formulas of classical p=F,q=F
  are closed under both relations but reject g and C.
- Common nontrivial survivor: the designated formulas of classical p=T,q=F
  contain g and C and are closed under both, but reject ¬p. Combination does
  not here force arbitrary formulas or an inconsistent pool.
- Indexed survivor: use the K3 and LP semantic theories of g as separate pools.
  Each retains its own closure and g, while both reject C. The result therefore
  does not silently transfer conclusions between context-indexed pools.

The closure proofs matter: raw countervaluations alone would not establish that
an alternative policy obeys all the retained consequence requirements. The
three deletions show necessity of each member of this **named sufficient input
bundle** for this fixed target, not globally weakest philosophical assumptions.
The separate-pool witness exposes the common-pool scope commitment.

## What this establishes, and what remains open

The conditional policy can demand a sentence that neither matrix alone demands
from g. This is more than taking the union of two lists of conclusions: the
joint inference uses an intermediate conclusion from each relation. It is not
a theorem that the global join equals classical propositional logic, that either
logic is correct, that pluralism is false, or that validity distinctions vanish.
The two validity relations remain explicitly incomparable in the certificate.

The strongest local pluralist/conventionalist accepts the separate pools and
rejects unindexed transfer or joint closure. A defender of a single policy must
justify its applicability and what epistemic force it has. Even if the policy
is accepted for a task, categorical authority and feasibility for actual agents
remain OPEN. A policy constraint on selected formulas is not itself an ought,
and no truth or obligation follows from merely performing an inference.

Wide-scope revision remains distinct: one may withdraw g rather than preserve
it and acquire C. The third deletion makes that mathematical possibility
concrete. It does not justify the withdrawal or select the right revision.
No normative warrant, objective-duty truth, worldview or root premise is closed.
Computed root-frontier comparison belongs to the PR/CI; intended delta: none.

Navigation used to orient this analyst test, **not verified attribution**:
[Logical Pluralism §2.2](https://plato.stanford.edu/entries/logical-pluralism/#NormObje),
[Bridge Principle options](https://plato.stanford.edu/entries/logic-normative/bridge-principles.html),
and [Many-Valued Logic](https://plato.stanford.edu/entries/logic-manyvalued/index.html).
No source, passage or claim records are introduced. The source-specific claims
and any argument for the policy's normative authority would need separate work.

## Rejected proof-engineering approach

The first compiled proof used simplification for Boolean and list-membership
steps. Its axiom probe reported `propext` and `Quot.sound`; narrowing the probe also
identified the core `Bool.and_eq_true_iff` and `Bool.or_eq_true_iff` helper
proofs as carrying these dependencies. Comparator
correctly rejected it under the required zero-axiom configuration. Neither the
frozen statement nor the matrix/policy semantics required those axioms: the
repair replaces these steps with direct Boolean case analysis and `List.Mem`
elimination. Weakening the permitted-axiom configuration was rejected. This is
a proof-term boundary, not a failure or weakening of the philosophical target;
the frozen Challenge and vocabulary remain unchanged. Final acceptance evidence
is supplied by the PR/CI on the delivered inputs.
