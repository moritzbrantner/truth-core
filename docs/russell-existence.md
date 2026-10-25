# Russell: quantification, individuals and explanation

Issue #273 is phase A of #272. It does not begin with a verdict that Russell is
false, or assume a Thomist account of existence. The verified English witness
covers the complete relevant Lectures V and VI, with immediate lecture-boundary
context: physical PDF pages 104–120 and 120–135 in the cited Routledge edition.
Conventional citations below refer to its **printed** pages 61–92. The original
lectures are distinguished from Pears’s introduction. No PDF text is committed.
The consulted ranges extract identically with Poppler 24.02 and 26.01; both the
response-byte hash and normalized extracted-text hashes are pinned.

## What the source commits to

| Question | Reading and locator | Corpus statement |
|---|---|---|
| A1: what is quantified existence? | A propositional function has a satisfying value; this does not give a fixed number or a named witness (V pp.66–68). | STMT-RUSSELL-NONEMPTY-ANALYSIS |
| Singular described existence | The description has at least one and at most one satisfying value (VI pp.86–87). | STMT-RUSSELL-DESCRIPTION-UNIQUE |
| Individual existence | Russell rejects the corresponding predicate of a directly named individual (V p.77; VI pp.90–91). | STMT-RUSSELL-INDIVIDUAL-RESTRICTION; STMT-RUSSELL-INDIVIDUAL-EXISTENCE-NONSENSE |
| Genuine names | A genuine name has a referent; significant apparently singular negative existence is analyzed through descriptions (VI pp.78–81). | STMT-RUSSELL-GENUINE-NAME-DENOTES |
| Actual number | Whether there is a universe and exactly how many things it contains are empirical matters, not logical theorems (V pp.75–76). | STMT-RUSSELL-EXACT-NUMBER-CONTINGENT |
| Completeness of the analysis | General and existence facts enter the world’s inventory, but the technical function treatment is expressly not offered as their whole analysis (V pp.71–72). | STMT-RUSSELL-GENERAL-FACT-ANALYSIS-OPEN |

The source’s use of “possible” in V means that a propositional function has a
satisfying value. It is not silently translated into possible-world diamond. The
immediate VII clarification on printed p.92 reinforces that limitation.

A2 must be separated into two proposals. Russell’s **semantic** restriction on
individual-existence predication is strongly stated in this range. The much
stronger assertion that A1 settles every meaningful explanatory question is not
established by it. In particular V p.72 prevents attributing a complete account
of general facts to the technical analysis alone. The separate modern
STMT-RUSSELL-EXPLANATORY-SUFFICIENCY is an additional test target, not a sourced
Russell premise.

A3 concerns actual instantiation, which individuals instantiate a predicate,
exact number, and possible grounds. We do not assume every such question has a
further answer. A primitive instantiation fact is an available reply whose
adequacy remains a philosophical question.

## Five mechanically checkable tests

`TruthCore.Modern.Russell.Existence` is the minimal typed interface. It imports
the existing modal fixture for the world-relative comparison; no Thomist or
Catholic premise enters. Existing participation/moral explanation types have
different relata, so they are not reused as if instantiation were participation
or a moral fact. The same predicate interpretation is literally held fixed in
the grounding test.

1. **RUSSELL-EXISTENCE-DESCRIPTION.**
   `Description.checks` proves the identity-characterization of a description
   equivalent to nonemptiness plus at-most-one satisfaction, for any typed
   domain, including an empty one. The forward direction extracts the witness
   and transports each satisfying value to it. The reverse uses the selected
   witness and uniqueness to establish the exact identity-characterization.
   No choice, excluded middle or nonempty-domain premise is used. This is a
   logical analysis, not a proof of explanatory adequacy.
2. **RUSSELL-EXISTENCE-CARDINALITY.**
   `Cardinality.checks` explicitly compares zero, one and two satisfying values
   on the complete two-label carrier. A one- and a two-member extension both
   satisfy the existential proposition but have different counts. Two singleton
   extensions have the same existential truth and number but different named
   witnesses. The description result is imported and applied, rather than
   restated as a premise. This agrees with Russell’s contingent-number point;
   it does not refute him.
3. **RUSSELL-EXISTENCE-GROUNDING.**
   `Grounding.checks` exhibits empty and single-edge directed grounding
   expansions of the same extension and the same fact-truth assignment. Both
   are asymmetric and sound at their endpoints, but disagree about whether a
   fixed candidate basis grounds a fixed instance. Therefore the additional
   `GroundingDetermined singleA` sufficiency target fails without restrictions
   connecting classification to admissible grounding. Nothing proves an actual
   basis, causal production, a need for every fact to have a ground, or the
   adequacy of either expansion as a complete metaphysics.
4. **RUSSELL-EXISTENCE-INDIVIDUAL.**
   `Individual.checks` uses the existing branching frame. The outer candidates
   remain fixed, each world is inhabited, and which candidate belongs to the
   actual domain changes. An unchanged optional name token can consequently
   fail to denote. A genuinely denoting name at a selected context still has
   an actual referent by its type; that does not give necessary existence.
   This proves coherence of the explicitly different semantics, not a
   contradiction inside Russell’s significance restriction or an attribution
   of varying domains to Russell.

5. **RUSSELL-EXISTENCE-PROJECTION.**
   `Projection.checks` uses two explicitly open inputs: the selected extension
   is realized, and a separately supplied instance-to-basis grounding norm
   holds. The proof takes the actual satisfying witness and applies that norm
   to it. Two fixed countermodels show why neither input can simply be omitted:
   the singleton with empty grounding has no grounded witness, and the norm
   holds vacuously on the empty extension. This is one conditional sufficient
   route, not a claim that every why-question needs this kind of answer or that
   Russell endorses the norm.

All five advertised consequences are accepted **within these typed systems**:
the first follows constructively, and the next three are actual finite
models evaluated with the stated assignments, and the fifth extracts a typed
grounded witness from its explicit hypotheses. Their Challenges freeze the
advertised propositions; Comparator/NanoDa checks the corresponding Solutions.
No result proves premise truth or closes a Catholic-case frontier node.

## Strongest objections and replies

- **“A quantifier does not explain what makes an instance actual.”** Correct as
  an independence observation in the specified expansion class. Russell can
  reply that logical analysis was the task, and that primitive facts or a
  separate theory can address further questions. The source’s own p.72
  concession makes this reply especially important. The independent expansions
  do not establish the answer to A3 or disprove A1.
- **“An existential proposition must determine its individuals and number.”**
  It need not. The finite witnesses separate these questions; Russell already
  treats actual number as contingent. Additional descriptions and predicates
  may identify witnesses or fix number without changing the meaning of A1.
- **“Individual existence is coherent in a varying domain.”** It is in the
  alternative supplied here. Russell can reject its treatment of outer
  candidates or significance conditions. Settling that disagreement requires
  defending a semantics, not transferring a theorem between logics.
- **“An explanatory addition vindicates an existential property.”** Merely
  adding a symbol does not vindicate its interpretation. A proposed ground
  must have independently defended content and a bridge to actual
  instantiation; a stipulated candidate-basis tag does not provide that
  defense. Nor does the test exclude an adequate primitive stopping point.

## Residual frontier and fidelity self-sweep

RUSSELL-EXPLANATORY-SUFFICIENCY asks whether a stronger exhaustiveness bridge is
historically or philosophically justified. RUSSELL-PRIMITIVE-INSTANTIATION asks
whether a primitive fact is an adequate stopping point. RUSSELL-INDIVIDUAL-SEMANTICS
asks which significance/domain conditions should be adopted. Their candidate
records identify the source range to revisit and do not fabricate new claims.
The conditional explanatory route exposes exactly two open inputs in the graph:
`python3 scripts/corpus.py frontier --root STMT-RUSSELL-GROUNDING-PROJECTION --reaching-root`.
They are STMT-RUSSELL-REALIZED and STMT-RUSSELL-INSTANCE-BASIS-LAW, both
unattributed, unestablished premises; the countermodels show their role in this
route without asserting the truth of either. The separate A2 sufficiency target
remains unestablished and is not identified with that sufficient A3 norm.
The adequacy and significance disputes remain unformalized research questions
in those candidates; the model tests do not silently close them.

Load-bearing definitions are linked from each result: DEF-RUSSELL-QUANTIFIER-EXISTENCE,
DEF-RUSSELL-DESCRIPTION, DEF-RUSSELL-INSTANTIATION and DEF-RUSSELL-FINITE-EXTENSION
fix predication, uniqueness, witnesses and count; DEF-RUSSELL-GROUNDING and
DEF-RUSSELL-EXHAUSTIVENESS fix explanatory edge and sufficiency; DEF-RUSSELL-ACTUAL-DOMAIN,
DEF-RUSSELL-CONTEXTUAL-NAME and DEF-RUSSELL-GENUINE-NAME separate alternative
semantics from source restriction. DEF-RUSSELL-LOGICAL-ANALYSIS states the
logical/explanatory boundary. DEF-RUSSELL-REALIZED, DEF-RUSSELL-BASIS-LAW
and DEF-RUSSELL-GROUNDED-EXISTENCE fix the conditional route without an
implicit actuality or universal-grounding premise. The linked DISAMB-RUSSELL-EXISTENCE,
DISAMB-RUSSELL-EXPLANATION and DISAMB-RUSSELL-NAMES record the choices preventing
scope or sense transfer.

Every attributed claim was checked against the complete materialized range.
The strong individual-predicate wording remains attributed, not weakened into
mere caution. The p.72 limit remains visible, not removed to manufacture A2.
Modern Bool valuations, typed candidates and grounding tags remain stipulations.
Quantifier identity, temporal/modal context and explanation are never equated.
The verdict is: A1 and singular-description analysis survive these tests;
extension-only explanatory sufficiency does not follow; an unrestricted A2 is
not established as Russell’s view in these passages. Whether a stronger
philosophical theory answers A3 remains open.
