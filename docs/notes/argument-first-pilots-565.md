# Argument-first pilots: Cogito to necessary being, and moral authority (#565)

This note applies the argument-first method of
[systematic-corpus-loop.md](../systematic-corpus-loop.md#frontier-investigations-argument-first-decomposition-on-demand)
to the two pilot investigations, #564 and #563. It reads only existing records;
it adds no statement, claim, argument or result, and changes no premise or
frontier closure. Every ID below exists on `main` at the time of writing.
Neither pilot currently lies on a root path: `corpus.py frontier --reaching-root`
lists none of their statements.

## Low-leverage splitting seen in recent work

Three recent cases show where an investigation lost its whole-case purpose:

1. **Cogito drafts #522–#525, #529.** Five branches defined "an occurring thought
   has a bearer" four times under different names, and two packed open premises
   into premise-free statements. PR #538 (#532) consolidated them into one
   vocabulary (`TruthCore.Logic.CogitoSubject`). The consolidated results are
   still transcriptions (`COGITO-SUBJECT-FROM-OCCURRENCE`), and no record yet says
   what the bearer is *for*: the downstream necessary-being argument appears in no
   Cogito record.
2. **Necessary-underived routes (PR #518).** Five derivations and five
   countermodels expose structural bridges, but every route takes an existing
   necessary individual as a premise (`STMT-KANT-CONVERSION-NECESSARY-WITNESS`).
   They refine what follows *after* the existence question, while the question
   that decides the case (why a necessary concretum exists at all) stays where it
   was. Useful, but the PR could not say which rival it weakened.
3. **#564's first route list.** Three routes (population, contingent thinker,
   three causal relations) with paired models for each were proposed before the
   owner's follow-up comment reduced them to one modal fork. Most of the proposed
   splits (kinds of thinker, kinds of causation) do not change any verdict of
   the fork below.

The pattern is the same: distinctions and conditional lemmas were produced
before the end-to-end case they serve was written down, so no one could tell
which of them was load-bearing.

## Pilot A: Cogito to a necessary concretum (#564, #487, #553)

**Thesis and purpose.** An actually performed thought, together with explicit
dependence and well-foundedness premises, entails that some de re necessary
concrete individual exists. It would supply an existence premise that the
necessary-being routes currently assume.

**End-to-end case.**

1. A thought occurs (`STMT-COGITO-THOUGHT-OCCURS`, open).
2. It has a bearer (`STMT-COGITO-EVERY-THOUGHT-HAS-SUBJECT`, open); together these
   give a thinking subject (`COGITO-SUBJECT-FROM-OCCURRENCE`, a transcription).
3. That bearer is a concrete individual existing at the actual world. **No record
   connects step 2 to step 4**: the Cogito vocabulary has no world, existence or
   concreteness predicate.
4. In a nonempty actual concrete world, either some necessary concrete individual
   exists, or there is a contingent root without a concrete predecessor under the
   selected grounding relation, or that grounding is not well founded
   (`BRUTE-ROOT-DISJUNCTION`, a non-transcription conditional with no premises).
5. Exclude the last two horns by a well-foundedness premise and an anti-brute-root
   premise. Neither is recorded; `POSSIBLE-CAUSE-BRUTE-SURVIVAL` shows that modal
   causal opportunity alone does not exclude a brute root.

The modal fork in the owner's #564 comment (the thinker is necessary or
contingent) is not needed: step 4 quantifies over every concrete individual, so
the thinker's own modal status never enters. The necessary-thinker branch is the
first horn of step 4.

**Strongest rivals, at the same questions.** (a) Event-only ontology: thought
without a distinct bearer (`COGITO-SUBJECTLESS-CONTROL`); step 2 is denied with a
replacement account, not merely subtracted. (b) Brute contingent foundation:
step 5's anti-brute-root premise is denied; the rival owes an account of why the
root exists, or records it as unexplained. (c) Non-well-founded grounding:
infinite or cyclic dependence. (d) Non-substantial bearer
(`COGITO-NON-SUBSTANTIAL-BEARER-MODEL`): harmless here, since step 4 needs only a
concrete existent, not a substance.

**Decisive missing bridge.** Step 3 (Cogito bearer to actual concrete existent in
the `BruteRootDisjunction` semantics) is the one connection worth a new canonical
statement; it is #536. The decisive fork is step 5: the weakest defensible
anti-brute-root principle (#505, #545). Kinds of thinker, kinds of causation and
the thinker's contingency stay in this note until a theorem needs them.

**Downstream.** If a necessary concretum is obtained, the existing routes
`NECESSARY-UNDERIVED-POSITIVE-LIFT` and `NECESSARY-UNDERIVED-POSITIVE-UNION`
continue to an underived one under their own open structural premises. Nothing
here reaches uniqueness, the divine attributes or the root.

**First formal slice (#564, 2026-10-27).** Step 5 was refined as the child
argument, and the thinker turned out to do work after all, though not through
its modal status. Relative to a fixed grounding relation, the global
anti-brute-root premise that excludes `BRUTE-ROOT-DISJUNCTION`'s root horn is
classically equivalent to "every actual contingent concretum has an actual concrete
ground" (an elementary equivalence, not formalized), so no weaker *global* principle closes that horn. Restricting both
premises to the bearer's ground-ancestry does: `COGITO-ANCESTRY-ROOT-FORK`
(occurring thought, bearer, concrete, existing at w₀, plus `Acc` at the bearer
for actual concrete grounding: a necessary concrete ancestor of the bearer or a
contingent root among its ancestors), then `COGITO-NECESSARY-CONCRETE-ANCESTOR`
(add the thinker-local anti-brute-root premise
`STMT-COGITO-THINKER-ANCESTRY-GROUNDED`). `COGITO-ANCESTRY-CONTROLS` shows both
local premises strictly weaker than the global ones (one model has the local
premises and a necessary, non-contingent thinker while both global premises
fail) and each premise needed. Excluded middle is explicit. Premise delta at
the root: none (`frontier --routes` and `--reaching-root` unchanged), since no
root-path premise is stated in world-indexed de re necessity. Next child: the
defence of the thinker-local anti-brute-root premise against the brute
contingent-foundation rival (#505, #545), or a bridge to the tertia via's
necessary being, which needs a modeling decision (`DISAMB-NECESSARY-INDIVIDUAL-SCOPE`).

## Pilot B: from objective goods to binding reasons (#563, #149, #185)

**Thesis and purpose.** A theory that claims to be a complete account of
categorical human morality must explain not only which acts are good or right but
why those standards apply to humans and give every relevant rational agent a
reason. This is a methodological standard for assessing completeness claims
(#563), not a proposition about what makes obligation binding.

**End-to-end case, per theory.** The shared answer map in
[naturalistic-moral-realism.md](../naturalistic-moral-realism.md) already asks
`Q-MORAL-GROUNDING` (goods and standards) and `Q-NORMATIVE-REASONS` (why pursue
the good) of Railton, Boyd and Catholic natural law, each answered **S**
(sourced, defense open):

- **Catholic natural law:** goodness as actuality and evil as privation
  (`AQUINAS-ST-I-Q5-A1-GOODNESS-FROM-DESIRABILITY`), the first practical precept
  (`STMT-FIRST-PRECEPT-OF-NATURAL-LAW`, sourced, open), satisfiable together
  (`CATHOLIC-NATURAL-LAW-CONSISTENT`). Its bridge from goodness to a reason binding
  every human is the precept itself; why the precept binds an indifferent agent
  is its open defense.
- **Railton and Boyd:** objective welfare or homeostatic goods, with reasons that
  are contingent and instrumental (`DEF-NATURALIST-CATEGORICAL-REASONS`). The
  stronger categorical requirement is the open attack
  `STMT-NATURALIST-CATEGORICAL-BRIDGE-OPEN`.
- **Anti-realists:** the emotivism, quasi-realism and expressivism results
  (`QUASI-REALISM-ADMITS-MORAL-ERROR`, `EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`)
  reject the realist formulation of the question rather than leave it unanswered.
- **Non-naturalist realism** (categorical reasons as primitive): no sourced
  record exists. It is the missing rival column.

**Existing discriminator.** `NATURALIST-RAILTON-ASCRIPTION-CONSISTENT` and
`NATURALIST-BOYD-ASCRIPTION-CONSISTENT` already give interpretations in which an
act is right or good although an agent has no instrumental reason to do it
(`STMT-RIGHT-WITHOUT-UNIVERSAL-REASONS`, `STMT-GOOD-WITHOUT-UNIVERSAL-REASONS`).
This is the rules-without-bindingness non-entailment for those fragments, with one
gap: their reason predicate is instrumental, and no predicate separates
applicability to humans from categorical bindingness. A new model pair is worth
building only for that separation.

**Decisive missing bridge.** The first precept's claim on an indifferent rational
agent, against the naturalists' contingent-reason answer. That is one sourced,
open premise on each side, not a new taxonomy of goods and roles. The
non-naturalist column needs a source before any formal test.

## Outcome and retain/revise

Premise delta: none for either pilot; no root-path premise is touched. What
changed is the selection of work: pilot A has one load-bearing connection (#536)
and one decisive fork (anti-brute-root), and drops the contingent-thinker route
as unnecessary; pilot B reuses an existing non-entailment instead of building a
new one and names one missing rival. Both cases can now be read in one page and
expanded into existing statement, argument and result records.

Retain the method. Revise after the first formal slice of each pilot: check that
the split proposed here (step 3 of pilot A; the applicability/bindingness
separation of pilot B) was in fact the one a theorem needed. No schema change was
needed; the existing records and one note sufficed.
