# Bidirectional proof exploration

The graph's proof exploration is an advisory projection of existing statement,
inference, argument and result records. It matches exact statement IDs only.
Equal wording, synonyms and apparent philosophical equivalence cannot merge
nodes. No new canonical graph, runtime service, axiom or witness is introduced.

Forward seeds come from `corpus.py frontier --json`'s established statements,
projected onto the graph. A selected scope can restrict these facts; selecting an
open statement cannot establish it. The forward search proposes applications of
recorded checked arguments only when **all** their premises are available. Its
newly reachable propositions remain proposals, distinct from authoritative
establishment. The graph's closure/status projection is never mutated.

Backward exploration enumerates existing inference applications into a selected
goal. Each application requires all its inputs (AND); different applications are
alternative branches (OR). Local assumptions and discharged assumptions remain
inspectable, and never become global forward facts. An inference without a
containing result remains visibly unverified. Reciprocal arrows with no ground
produce no forward facts. Search failure means unresolved, not refuted.

Exact-ID junctions propose a composition. Their argument/result provenance and
each branch's remaining premises can be inspected. A proposed meeting is not a
new verified result: record its precise statement, frozen Challenge, Solution,
inference composition and result, then pass Lean, binding checks, Comparator and
NanoDa. Existing source, interpretation, definition and empirical obligations
remain visible after formal consequence is checked.

The search visits a deterministic, bounded number of work items (at most 10,000),
memoizing goal/argument, selected scope and available-premise situations for that
run. It yields regularly to the browser event loop for cancellation. A changed
goal, budget, scope or graph discards the old run. The budget is a useful-search
bound, not a shortest-proof guarantee; exhausted/cancelled runs report partial
results and cannot trigger a claim that reuse has failed.

When a completed search cannot reach its goal, a transient, explicitly unverified
and unformalized intermediate-lemma suggestion joins the existing derived
research queue. It lists its intended bridge, missing premises, exact search
provenance, and source/definition/disambiguation/formal-verification needs. It
creates no corpus statement or fabricated source-range candidate. Actual research
still uses the existing source-range candidate pipeline.

## Checked pilot composition

`PILOT-COMPOSED-WITNESS` imports the #207 pilot's independent proof of
`STMT-SOME-LEAN-PROPOSITION-HOLDS`, applies the existing
`someImpliesNotAll` theorem to produce
`STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS` as an actual intermediate proof, then applies the checked `pairFromConsequence` B → C helper to construct `STMT-PILOT-WITNESS-AND-CONSEQUENCE`. The helper imports the existing reciprocal B → A result to recover the witness, then introduces the conjunction. The composed argument reuses all three existing pilot inference records and adds conjunction introduction. It has no premises or
permitted axioms. This is a bounded logical fixture, not philosophical progress
on the Catholicism root or verification of external truth.

The existing pilot stability bridge provides the non-meeting: a checked
conditional from `STMT-PILOT-LOGICAL-SENTENCE-STABLE` does not establish its
conclusion while that interpretation premise remains open. Synthetic fixtures
also exercise partial AND obligations, independent OR branches, ungrounded
cycles, scope restrictions, budget exhaustion and cancellation.

## Reformalization rounds: lessons from computational hermeneutics

Method note for #350 (split from the #342 prior-art survey). It changes no
premise and adds no record kind; the contract in `AGENTS.md` stays binding.

### Sources read

- **[FB19]** D. Fuenmayor and C. Benzmüller, *A Computational-Hermeneutic
  Approach for Conceptual Explicitation*, arXiv:1906.06582**v2** (19 July 2019;
  PDF sha256 `d41563a4a6cbbfba26cc5ff43adf0534d705b0a1b4ca859db2498a3740af1cfa`),
  §§3.3–3.5 and 4.2. Published in the Springer *Sapere* volume *Model-Based
  Reasoning in Science and Technology*, DOI 10.1007/978-3-030-32722-4_25 (not
  read in that edition).
- **[AFP-Lowe]** D. Fuenmayor and C. Benzmüller, *Computer-assisted
  Reconstruction and Assessment of E. J. Lowe's Modal Ontological Argument*,
  Archive of Formal Proofs, September 2017, entry `Lowe_Ontological_Argument`.
  Read from the release tarball `afp-Lowe_Ontological_Argument-2026-10-26.tar.gz`
  (sha256 `6c834d656abba2255c3bf6e28dafbc83bc8bf1cab1d3a6721eb57e014889e4b4`):
  theories `LoweOntologicalArgument_1`–`_7` and the generated document, §§2.2–2.8.
- **[KBZ]** D. Kirchner, C. Benzmüller and E. N. Zalta, *Mechanizing Principia
  Logico-Metaphysica in Functional Type Theory*, arXiv:1711.06542**v4** (24 July
  2019; PDF sha256
  `b142f229376cf295badb9f7ebee5979eb6cdca3cbedac3546e8eec64ecf1b569`), §§1, 5, 6.
  Published in *The Review of Symbolic Logic*, DOI 10.1017/S1755020319000297
  (journal pages not read).

These are method references, not corpus sources: no claim cites them.

### What they did

[AFP-Lowe] reconstructs Lowe's argument (P1–P8, C1–C10) in seven *iteration
series*, one theory file each. Round 1 proves C1, C5 and C7 and gets Nitpick
countermodels for C8–C10 even in S5 (§2.2). Each later round changes one
hypothesis, guided by the last countermodel. The C10 countermodel has a
necessary being that is abstract here and concrete elsewhere, so the authors
add "abstractness is essential". The next one has non-existent concrete beings,
so they add "concreteness entails existence". Then C10 is proved with axiom B,
and the proof does not use the T and 4 axioms that were also assumed (§2.3).
After every change they re-run the same three checks: a model of all axioms
(`nitpick[satisfy, user-axioms]`) and countermodels to necessitism and to modal
collapse, "since both would trivially validate the argument" (§§2.2–2.3,
note 7). Proofs that also never used the definitions of existence and
dependence led to a much simpler non-modal variant (§§2.5–2.6). That variant is
explicitly "not concerned with the interpretation of the original" anymore.

[FB19] generalizes this. Each candidate formalization extends a working theory,
and the interpreter looks for the missing axioms that make it valid "without
rendering it inconsistent or question-begging" (§3.5). Candidates are rated by
Peregrin and Svoboda's inferential criteria (§3.4): *reliability* (no valid form
licenses an intuitively incorrect natural-language argument) and
*ambitiousness* (validate as many intuitively correct ones as possible).
Under a principle of charity they "assume from the outset that the argument's
conclusions indeed follow" (§3.3), and they remove settled postulates once they
become jointly inconsistent (§3.5 note 16).

[KBZ] embedded Abstract Object Theory in Isabelle/HOL with layers of
abstraction so that *artifactual theorems*, which hold of the Aczel model but
are not theorems of the theory, are not derived (§§1, 4, 6). Trying to show that
β-conversion holds in the model for λ-expressions with certain definite
descriptions failed. The assumption that it holds then proved inconsistent:
the known Clark–Boolos paradox, re-entering through a new route, which led to a
revision of PLM (§5). (#342 calls it "previously unknown"; the paper says the
paradox was known and the route was new.)

### What we already do

- **Countermodels per step.** Omission countermodels (for example
  `premisesNeeded` in [act-potency-theory.md](act-potency-theory.md)) and the
  registered finite models with `corpus.py models --check/--argument`
  ([finite-models.md](finite-models.md)) play Nitpick's role, but certified in
  Lean instead of found by a model finder.
- **Hidden premises become explicit.** Where [AFP-Lowe] adds "abstractness is
  essential" or axiom B to make C10 valid, invariant 9 forbids adding it silently.
  It becomes an explicit, unattributed open premise or a candidate, and the
  frontier counts it.
- **Inconsistency as a result.** The configuration elimination loop
  ([configuration-elimination-loop.md](configuration-elimination-loop.md)) and
  theory verdict hygiene (#471) certify minimal inconsistent cores and
  satisfiable omissions, and report unknown otherwise.
- **No artifactual theorems.** Frozen Challenges, bind-check and the rule
  "existence of a witness versus properties of the particular witness"
  (`AGENTS.md`, step 8) keep facts about one model from passing as theorems of
  the theory.

What we do **not** adopt is charity as a proof rule. [FB19] discards
formalizations under which the conclusion does not follow. Here a failed
derivation stays a failed attempt or an open bridge (invariants 8–9, 12), and a
variant that stops interpreting the source, like [AFP-Lowe] §2.6, is a new
argument with its own statements, not a revision of the old claim.

### How rounds fit argument-first work

Reformalization rounds answer the **decisive fork** of an end-to-end case
([argument-first method](systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand),
#565). They do not split every sentence. [AFP-Lowe] works the same way: the
whole argument is formalized first, and each round changes only the hypothesis
that the current countermodel to the *main* conclusion points at. A round here:

1. starts from the step where the end-to-end case currently breaks (a failed
   bridge, a countermodel or an unproved conclusion);
2. changes one thing: adds, removes or replaces a premise, definition or
   logic/frame condition, each a statement with its own sourcing status;
3. re-runs the same checks: validity or a certified countermodel; a joint model
   of the premises (#569); a model where modal collapse and necessitism fail
   (#570); and no listed premise left unused by the proof (#571);
4. records the outcome in one `corpus/attempts/` record for the investigation.
   That record holds the change, the countermodel or theorem, and an adequacy
   note (does this reading validate an inference the source would reject, or
   lose one it makes?). Promote a new statement only when it passes the
   decomposition gate.

Rounds stop when the fork is resolved or reduced to a named open premise. They
also stop when the next change would leave the source's reading, at which point
the result is a new argument. A valid round is still only a conditional result:
its added premises stay on the frontier until sourced or proved.

### Adopted checks

- #569: joint-premise witness coverage for root-path results (consistency
  before proving from a premise set).
- #570: anti-trivialization witnesses with no modal collapse or necessitism.
- #571: flag result proofs that ignore a listed premise hypothesis.
