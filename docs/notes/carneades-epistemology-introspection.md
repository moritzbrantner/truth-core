# Carneades epistemology: justification and higher-order ignorance

Owner-authorized broad epistemology intake, 2026-10-28. This linked research
note preserves the readings and rejected inferences for
`ATTEMPT-CARNEADES-JUSTIFICATION-INTROSPECTION`. It is not a new handoff or an
attributed corpus claim. Actual and intended root-premise delta: zero.

## Public readings and attribution boundary

Read the complete public article [One Quarter of Americans Are Philosophical
Skeptics](https://www.carneades.org/post/one-quarter-of-americans-are-philosophical-skeptics),
including its methodology, and the [About page](https://www.carneades.org/about),
section “Skepticism”. No login, payment or private data was used. These are
unmaterialized public-page readings; no source claim or passage manifest is
created. A source attribution in the corpus would require a pinned
`web_snapshot`, successful materialization, and renewed contextual reading.
The formal profile below is independently stipulated, not attributed to the
article or to an ancient sceptic.

Precise reading locators and rejected interpretations:

- Article, introductory survey discussion, paragraphs beginning “The next
  question” and “Given that the two statements”: distinguishes higher-order
  justification doubt and certainty doubt, and allows sceptical scenarios
  without loss of knowledge.
- “Methodology Specifics”, second multiple-choice question, option 3: lack of
  knowing justification. Reject its replacement by lack of justification.
- “Aesthetics and Views on the Afterlife Associated with Skepticism”, first
  and third paragraphs: later paraphrases suppress those qualifications.
  Reject deriving epistemic impossibility from these survey classifications.
- About, “Skepticism”, substantive paragraph: distinguishes suspension from
  asserting impossibility. Reject applying retorsion to an unasserted claim
  of knowing universal ignorance.

These are methodological distinctions, not evidence that respondents have
true beliefs, that a respondent satisfies any formal norm, or that a sceptical
scenario actually obtains. Statistics are not premises of the proof.

## Investigation brief and strongest rivals

**Target:** identify the bridge from absence of knowing one's justification to
absence of first-order knowledge, separately from the structure of reasons.
Downstream purpose: prevent a regress argument or survey classification from
silently importing a higher-order access requirement.

**Reuse:** `TruthCore.Modal.Frame`, `Holds`, `Reflexive`, `Transitive`, and
`TruthCore.Modal.axiom4_valid` are reused exactly. The existing
`TruthCore.Results.Logic.RegressSchema.justificationTransfer` gives finite
ancestry for `GeneratedWarrant`, explicitly not epistemic justification.
Its `allPremiseBoundary` already separates a supported branch from support of
all inferential premises; its infinite/cycle controls are not new here.
`TruthCore.Results.Logic.KnowledgeRetorsion.noFactiveKnowerOfUniversalNoKnowledge`
excludes knowing universal ignorance under factivity; it does not exclude
suspension or establish knowledge. Its dossier was inspected.

**Strongest case:** a globally applicable knowledge-requires-justification norm,
combined with positive introspection, lets an agent who knows p know that p is
justified. Lack of the latter then excludes the former. Transitive epistemic
alternatives provide a sufficient structural condition for that step.

**Strongest rival:** first-order knowledge may require justification without
higher-order access to justification. A nonintrospective or externalist account
can reject the positive-introspection requirement. The explicit finite model
shows this is a consistent rival in the selected relational profile, even with
factivity. It does not establish that this profile captures actual knowledge.

Foundationalism, coherentism and infinitism concern the source/structure and
adequacy of justification. None by its name supplies either positive
introspection or its denial. A foundationalist could admit justified basic
beliefs without reflective access; a coherentist needs an adequacy standard
beyond a graph cycle; an infinitist needs one beyond an infinite predecessor
assignment. The existing generated-warrant semantics selects a foundationalist
standard and cannot refute the other standards merely by excluding their
warrant under that definition. No causal-grounding relation is identified with
epistemic support. These live alternatives are not settled by this result.

**Missing step and exact proof target:**
`TruthCore.Logic.JustificationIntrospection.IntrospectionBoundary` pairs:

1. For any shared Kripke frame F and world predicates p and J, transitivity plus
   `∀ w, Knows F p w → J w` entails, at every w,
   `(Knows F p w → Knows F J w)` and its constructive contrapositive.
2. A reflexive, nontransitive frame on `Fin 3`, with some actual world, satisfies
   that same global norm and `Knows F p actual ∧ J actual ∧ ¬ Knows F J actual`.

Here J means justification of this fixed p. `Knows F J` means knowledge of that
justification. The universal norm is needed at epistemic alternatives, not
only the actual world. Reflexivity makes relational knowledge factive. The
model has edges 0→0, 1→1, 2→2, 0→1 and 1→2, but not 0→2; p is true at 0 and 1,
and J holds only at 0. Only 0 knows p. The norm holds at every world and the
failure of higher-order access occurs at 0.

**Premise comparison:** no global norm, introspection principle or actual
knowledge token is established. They are explicit conditions inside the
quantified transfer; the norm is also checked in the countermodel. No source
claim, new axiom, source-derived truth, closed root premise, or actual
foundational/coherent/infinitist adequacy thesis is added. Root-path open
premises retained unchanged, added zero, removed zero. This is a nontrivial
conditional composition and omission control, not a discharge of scepticism.

## Verification boundary

The coordinator's shared service elaborated the final inlined declarations
with no errors and printed no axioms for `introspectionBoundary`. Response:
workspace `/home/brantner/privat/truth-core-sprint-proof`, HEAD
`49b4589aa6744c91a6bc9adec13215d0e7245c9d`, dirty preview, shared session
`causal-harvest`, virtual file `Scratch/carneades-epistemology.lean`, version 16,
content SHA256
`1650fbfae5f231d30aec51da52868234980441e2856ac44843c0dc5d467d0c91`.
The submitted content was the vocabulary followed by the Solution with its
local vocabulary import removed, plus `#print axioms` for the package theorem.
Requests used the coordinator's exclusive `/tmp/truth-core-lean.lock` lease.
This is interactive preview evidence, not Comparator, binding or NanoDa
certification of the committed revision. Final CI provides those boundaries.

The final proof uses explicit bounded `Fin` constructors and elementary Nat
elimination to retain the repository's zero-axiom policy. Rejected development
shortcuts (`omega`, ordinary Fin numerals/decidable Fin equality, and
`Fin.cases`) brought extensionality or quotient axioms through core helper
proofs; they were removed rather than enlarging the permitted-axiom list.

Claim/type self-sweep: the statement, inference, argument and result describe
exactly the universally conditional transfer plus the existential model. The
model asserts its own reflexivity, norm and nontransitivity; no universal
ignorance or certainty property is claimed. Definitions and disambiguation
records distinguish first-order knowledge, justification and higher-order
knowledge and explicitly exclude metaphysical accessibility and assertion.
