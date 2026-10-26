# Causal branching, existence-PSR, and explained sources: formal syllogisms

This is a **source-free conditional** research note for the causal regress and
necessary-being investigation. It connects CAU-07/08, the finite-to-infinite
bridge, #367/#441, and the existence-PSR line without silently presupposing
Thomism, divine simplicity, or any source's claims. All sound conclusions
are consequences *within the precise predicates named here*. The premises'
metaphysical truth is a different frontier.

## I. Two independently checked arguments

### S1. Finite local fan-in + well-foundedness ⇒ finite total ancestry

1. Every node has finitely many *immediate* causal predecessors.
2. The direct predecessor relation is *well-founded* (in Lean's `Acc` sense).
3. **Therefore**, every node has finitely many *distinct transitive* causal
   ancestors.

Formal proof: `TruthCore.Causality.FiniteBranching.finiteAncestry_of_wellFounded_finiteImmediate`,
wrapped as the independent result
`CAUSAL-FINITE-BRANCHING-TO-FINITE-ANCESTRY`. The induction combines each
finite immediate-predecessor set with the inductively finite ancestor sets of
its members, using Mathlib's finite union. There is **no uniform upper bound**
on the size of these finite ancestral cones and no finite global history.

The exact premises both matter:

- **Infinite fan-in despite well-foundedness**: a single node `none` has all
  `some n` as immediate predecessors, each of which has none. The graph is
  well-founded and has no chain of length two, but the root has infinitely many
  distinct ancestors (`infinitelyWideStarWellFounded`,
  `infinitelyWideStarNotFiniteAncestry`).
- **Infinite regress despite finite fan-in**: each natural-number node `n` has
  exactly one predecessor `n + 1`. Each node therefore has finite direct
  fan-in, yet the relation is not well-founded
  (`successorPredecessorFiniteImmediate`,
  `successorPredecessorNotWellFounded`).

With finite fan-in, the earlier proof of finite ancestry **and** exclusion of
causal loops establishes a converse: these conditions are jointly equivalent
to well-foundedness. That reuses #367's result rather than inventing a new
well-foundedness argument.

### S2. Populated world + existence-PSR + well-founded causes ⇒ explained source

1. At least one individual actually exists at the selected world.
2. Every existent has an explanation token for its existence fact
   (`ExistencePSR`).
3. The world's entire modeled direct-cause relation is well-founded.
4. **Therefore**, some existent has an explanation token for its existence
   fact but no **incoming cause from any existing individual** at that world.

Formal proof: `TruthCore.Explanation.WellFoundedSource.psr_gives_explained_source`,
wrapped as `PSR-WELL-FOUNDED-CAUSE-HAS-EXPLAINED-SOURCE`. The proof first
finds a cause-minimal existent by accessibility induction; only **then** uses
PSR to obtain its reason. A candidate nonentity may be in the constant
domain; the conclusion excludes *existing* incoming causes, not every possible
relation to a nonexistent candidate.

The reason is **not** shown to be metaphysically adequate, an efficient cause,
an intrinsic sufficient reason, a necessary being, a unique source, or God.
No modal identity preservation or cross-world causal condition enters.

## II. Three minimal-configuration controls

S2 has a deliberately weaker causal core: **population + causal
well-foundedness** alone imply that *universal external causation* is false.
PSR is **not needed** for that incompatibility. It is needed only to say that
the uncaused existent also has a modeled existence explanation. Precisely:

| Configuration | Populated | Existence-PSR | Causes well-founded | Every existent externally caused | Explained source |
| --- | --- | --- | --- | --- | --- |
| Existing `MODEL-PSR-INTRINSIC` | yes | yes | yes | no | yes |
| New `MODEL-PSR-MUTUAL-CAUSES` | yes | yes | no | yes | no |
| New `MODEL-PSR-EMPTY-WORLD` | no | vacuous | yes | vacuous | no |

The mutually causing pair and empty-world model are explicitly implemented in
`TruthCore.Explanation.WellFoundedSource`. They isolate two independent
omission errors: deleting well-foundedness allows all-external causation, while
deleting an actual existence witness makes *any* universal causal claim
vacuous. A cyclic **finite** witness does not establish that infinite acyclic
regress is metaphysically coherent. That remains a separate investigation.

## III. Six further syllogisms or forks to investigate

These are **research obligations** unless a formal result is explicitly cited.
Their claims must not be promoted to established metaphysics solely because
Lean verifies an implication conditional on proposed premises.

1. **S3 — Causal acyclicity does not give causal sources. Verified.** The
   reverse-successor relation on naturals has no nonempty finite causal cycle
   (`reverseSuccessorNoLoops`), but every node has a predecessor and no global
   source exists (`reverseSuccessorNoGlobalSource`). Mere acyclicity cannot
   eliminate infinite regress. This infinite carrier is Lean-checked directly,
   not improperly entered in the *finite*-model registry.
2. **S4 — Finite-subsystem grounding need not imply global grounding.
   Verified.** The same infinite acyclic chain has a source in *every*
   nonempty finite induced restriction: choose its maximum natural number.
   Nevertheless the full infinite graph has no source at all. The compound
   Lean theorem `TruthCore.Causality.FiniteRestriction.finiteLocalSourcesAndNoGlobalSource`
   checks both quantifier scopes; independent result
   `CAUSAL-FINITE-LOCAL-WITHOUT-GLOBAL` packages the existential countermodel.
   This is a precise compactness/finite-to-
   infinite counterexample, not an argument for the physical possibility of
   an actual infinite causal past.
3. **S5 — Per se no-regress from the stronger finite-ancestry condition.**
   Already conditional in #367: finite distinct ancestry + no cycles + an
   explicit inclusion of per se links rules out infinite descending per se
   chains. Bridge S1 gives a *possible route* to one premise, not a defense of
   the other premises or of a globally finite past.
4. **S6 — Necessary existence of *something* vs one necessary individual.**
   A modal model can have a nonempty roster at every accessible world but
   rotate which individuals exist. Thus the quantifier shift from
   `□∃x Exists(x)` to `∃x□Exists(x)` requires another premise. The earlier
   necessary-individual corpus tests cover this distinction; do not identify
   S2's explained local source with a single world-invariant being.
5. **S7 — A causally uncaused source is not automatically an ungrounded fact.**
   Distinguish the cause of an entity from the reason for its existence fact.
   Both intrinsic-reason and externally dependent-reason interpretations must
   be tested with independently stated adequacy conditions; existence-PSR is
   not the same as `EveryExistentExternallyCaused`.
6. **S8 — Necessary source, simplicity and uniqueness are downstream.**
   If and only if additional modal/explanatory bridges are defended, test
   whether a source may be composite, multiple, contingent or without
   explanatory self-sufficiency. Keep countermodels for each omitted bridge;
   do not attach the name God to an anonymous root by definition.

## IV. What actually moved

- The **formal frontier** advances: three exact result statements now have
  checked, challenge/solution-separated Lean proofs, three independently
  interpreted finite model profiles delimit S2's assumptions, and a fourth
  **infinite symbolic model** blocks two tempting quantifier shifts.
- The **philosophical frontier** is still open at the applicability of
  well-foundedness, a relevant local finite-fan-in causal interpretation,
  and genuine (rather than stipulated) sufficient explanations.
- Adjacent compactness and necessary-disjunction investigations are already
  tracked in GitHub #484 and #485. Do not duplicate their work here; use S4
  and S6 to bring their eventual proofs or countermodels into this graph.

Principle for reassembly: prove the implication; give its *smallest* explicit
premise set; search for omission countermodels; then separately justify the
premises. Every validated node is reusable by later arguments, and every
unproved metaphysical bridge remains visible at the frontier.
