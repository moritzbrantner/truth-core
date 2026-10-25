# K: collapse, sinks and branching

Issue #262 investigates the **stipulated mathematical semantics** of
`ResearchFixture`; K supplies an arbitrary accessibility relation. Nothing here
identifies a formal state with a genuine metaphysical possibility, establishes
real-world contingency, or attributes an unrestricted bridge to Hume. The
source-fidelity investigation remains #268. No Catholic or Thomistic premise,
Scott positivity axiom, external solver or additional Lean dependency is used.

## What follows without frame conditions

The result `MODAL-K-LAWS`, bound to
`TruthCore.Results.Modal.K.Laws.checks`, proves:

| Statement | Exact domain/assumptions |
| --- | --- |
| `MC(w) ↔ ∀v, Rwv → v=w` | All world predicates; arbitrary frame/root |
| `MC(w) ↔ ∀P, ◇P(w) → P(w)` | All world predicates; arbitrary frame/root |
| `MC(w) ∧ □MC(w) ∧ ¬◇MC(w)` at a sink | Any domain; explicitly no successors |
| `MC(w) → ¬(◇P(w) ∧ ◇¬P(w))` | Full MC; any supplied predicate P |

Full comprehension admits the root-equality predicate. Applying MC to it proves
successor identity; conversely equality transports any truth. Possibility entails
actuality gives the same identity restriction by applying it to equality with an
accessible witness. The contingency contradiction transports its two witnesses to
the root. These arguments use neither excluded middle nor world extensionality.
They could fail on restricted domains: `MODAL-K-SCOPE-BOUNDARY` supplies the
counterexample below.

Successor identity says **at most** the root is accessible. It does not supply a
successor, assert reflexivity, or identify inaccessible worlds. In particular a
sink satisfies MC and □MC vacuously while ◇MC is false. A universal statement over
an empty successor set proves no cosmological existence claim.

## Finite countermodels with independent contingency

`fork link` explicitly enumerates `[root, sink, branch, remote]`.

| World | Successors, `link=false` | Successors, `link=true` | Atom p |
| --- | --- | --- | --- |
| root | sink, branch | sink, branch | false |
| sink | none | none | true |
| branch | none | sink | false |
| remote | remote | remote | true |

There are no cross-component edges to remote. It is a distinct collapsed state,
not a world that root-relative quantifiers secretly include. K assumes no
seriality, reflexivity, symmetry or transitivity. These finite relations are
witnesses, not claims that every K frame has their properties.

`MODAL-K-COUNTERMODELS`, bound to
`TruthCore.Results.Modal.K.Countermodels.checks`, proves the following for **both**
all predicates and the complete fixed formula language with the displayed atom:

| Root evaluation | Fork | Chain-fork |
| --- | --- | --- |
| Actual MC | false | false |
| Possible MC | true, witness sink | true, witness sink |
| Necessary MC | true | false, counterexample branch |
| `◇p ∧ ◇¬p` | true, witnesses sink / branch | true, witnesses sink / branch |
| `∀P, ◇P → P` | false, witness p | false, witness p |

The atom valuations and accessibility independently construct contingency;
neither possible collapse nor a conceivability bridge is used to obtain it.
The root fails language MC already for the expressible sentence ¬p, which is
true at root and false at sink. Full MC then also fails. Thus possible MC implies
neither actual MC, necessary MC, nor the absence of contingent alternatives in K.
Necessary MC also does not imply actual MC: the fork is a counterexample. The
chain-fork prevents treating the fork's necessary MC as a consequence of possible
MC. None of these models refutes Hume's narrower source argument.

`MODAL-K-EXTENSIONALITY`, bound to
`TruthCore.Results.Modal.K.Extensionality.checks`, proves both fork languages
satisfy `PropositionalExtensionality`. Agreement on the atom, `◇(⊥→⊥)` and `□p`
forces equality of the four state labels: their Boolean signatures differ for
every pair. This uses the shared evaluator-correctness theorem and finite case
analysis, not an axiom. The displayed countermodels therefore survive the
**optional world-extensionality configuration**. The full domain is extensional
for any type by equality-predicate separation; no extra assumption is needed.

## Restricted language and the identity boundary

`MODAL-K-SCOPE-BOUNDARY`, bound to
`TruthCore.Results.Modal.K.ScopeBoundary.checks`, composes the existing shared
`duplicates` fixture. It has two labels, universal accessibility, and a constant
atomic valuation. All formulas agree. At false, fixed-language MC, ◇MC, □MC and
language-relative `∀P, ◇P→P` hold. Full-predicate MC and full-predicate
`∀P, ◇P→P` fail: equality predicates distinguish the labels. Fixed-language world
extensionality fails. This is a comparison of domains, not an argument that
renaming a world creates a different metaphysical possibility.

The same result proves a separate conditional upgrade for an arbitrary domain:
**excluded middle + negation closure + world propositional extensionality +
domain-relative MC ⇒ full-predicate MC**. It composes shared
`extensional_separates` with the K successor characterization. Every extra
assumption is quantified explicitly. The duplicate fixture shows that dropping
extensionality blocks this route even with a negation-closed fixed language.
Full comprehension instead supplies equality directly, so that route needs
neither excluded middle nor an extensionality assumption. No result silently
switches domains or treats the corpus inventory as complete.

## Reproduction and verification boundary

```bash
lake build
lake env lean --run scripts/modal-k.lean
scripts/verify-result.sh MODAL-K-LAWS
scripts/verify-result.sh MODAL-K-COUNTERMODELS
scripts/verify-result.sh MODAL-K-SCOPE-BOUNDARY
scripts/verify-result.sh MODAL-K-EXTENSIONALITY
```

The deterministic report prints both models in the enumeration order above.
Each row is `(root, [(target, edge), ...], p, □p, ◇p, accessible p witnesses,
accessible counterexamples to □p)`. At the common root its p-witness list is
`[sink]`, and its ¬p-witness and box-counterexample lists are `[branch]`. These
exact lists and Boolean formula values are part of the frozen countermodel
contract. The shared evaluator checks formula truth, not an enumeration of all
Prop-valued functions; full-domain claims are proved separately with quantified
Lean terms.

All four corpus arguments have no premise statements: their exact assumptions
are inside universally quantified conditional laws or explicit finite models.
They are structured proofs/countermodels, not opaque bridge transcriptions.
Challenges freeze each advertised contract and Comparator permits no axioms.
Verification establishes these semantic consequences only; adopting a frame,
proposition domain, conceivability bridge or independently warranted contingency
for metaphysics remains a separate philosophical task. No frontier closure or
source-derived premise is advertised.

## Fidelity and definition self-sweep

There are no new attributed claims or primary-source paraphrases in this slice.
`DEF-MODAL-FIXTURE-FRAME`, `DEF-MODAL-FIXTURE-DOMAIN` and
`DEF-MODAL-FIXTURE-MC` define the shared terms. Identity, agreement and optional
extensionality use their existing separate definition records.
`DEF-MODAL-K-ACTUALITY` defines the reverse modal direction;
`DEF-MODAL-K-FORK` specifies the finite states, edges and valuation;
`DEF-HUME-TEST-CONTINGENCY` supplies the reused model-relative predicate.
`DISAMB-MODAL-FIXTURE-SCOPE-IDENTITY` and
`DISAMB-MODAL-K-COLLAPSE-MODES` distinguish proposition domains, world identity,
actual/possible/necessary collapse, and metaphysical interpretation. Each new
statement and argument links these records. The four proof explanations above
state the conclusion, exact assumptions, witness/derivation and binding theorem;
no missing philosophical premise was inserted to obtain a proof.
