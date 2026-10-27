# Shared roots, empty extensions, and modal necessity

This investigation is an **unattributed mathematical diagnostic** following
the existing necessary-individual quantifier controls. It connects a shared
foundation across histories with a modal empty-extension fork and a finite
in-world causal relation. It does not formalize Graham Oppy's writings as a
source claim: no pinned passage has been materialized for that purpose. Nor is
either finite frame independently established to be metaphysically possible.

## Exact intermediate result

For fixed roster `I`, world carrier `W`, Kripke accessibility `F`, presence
extension `present`, and starting world `w`, set:

```
SharedRootOnPopulated F present w r :=
  ∀ v, F.access w v → (∃ x, present x v) → present r v

DeDicto F present w :=
  ∀ v, F.access w v → ∃ x, present x v

DeRe F present w :=
  ∃ r, ∀ v, F.access w v → present r v
```

`NECESSARY-INDIVIDUAL-SHARED-ROOT-BRIDGE` is the constructive equivalence

```
DeRe F present w ↔
  (DeDicto F present w ∧ ∃ r, SharedRootOnPopulated F present w r)
```

The nonempty-accessible-world premise is indispensable to the backwards
direction. Merely adding an explanation for *dependent things in populated
histories* cannot silently discharge it. This says nothing by itself about
*why* that root exists, or whether the frame actually represents all
metaphysically possible worlds.

## Two exhaustive finite checks

`NECESSARY-INDIVIDUAL-ROOTED-EMPTY` uses three universally accessible worlds
and three rigid individual labels. The world and individual domains both happen
to use `Fin 3`, but their semantic roles are given by separate argument
positions. The existence extension is:

| World label | Present individual labels | Present cause edges |
| --- | --- | --- |
| 0 (empty extension) | none | none |
| 1 (history A) | 0 (root), 1 (dependent A) | 0 → 1 |
| 2 (history B) | 0 (root), 2 (dependent B) | 0 → 2 |

World `1` is the stated actual point of evaluation. It accesses the empty
extension at world `0`; its own presence extension is nonempty. Every present
nonroot has a cause in the **same** world. No two causal edges compose, so
there is no infinite causal ancestry even inside this stipulated model.
Nonetheless the fixed root fails `DeRe`: it is absent at world `0`. The model
also fails `DeDicto` and satisfies `JointAbsence`.

`NECESSARY-INDIVIDUAL-HISTORY-RESTRICTION` retains precisely worlds `1` and
`2`'s presence extensions, relabeled `false` and `true`, with all-to-all
accessibility. Its root is now `DeRe`, and `DeDicto` holds. Neither the
individuals nor the two populated histories were changed. Only the presence
of the accessible empty extension differs. These paired controls expose the
choice of *which worlds are admitted*, not a proof in favor of either choice.

The biconditional and earlier alternating-witness control give this small
configuration calculation (`S` = some fixed root across *populated* worlds;
`P` = all accessible worlds populated):

| `S` | `P` | `DeRe` | Relevant interpretation |
| --- | --- | --- | --- |
| yes | yes | yes | New two-history restriction and generic bridge |
| yes | no | no | New rooted/empty three-world control |
| no | yes | no | Existing `NECESSARY-INDIVIDUAL-ALTERNATING` control |
| no | no | no | Logical consequence of the bridge; no separate model registered in this slice |

The two *independent* omission countermodels are important: excluding the
empty world alone is insufficient if the root changes identity between
histories; positing one shared root across populated histories alone is
insufficient if an empty extension remains admissible.

## Inferences we may and may not draw

1. **Proved conditional:** Shared root plus population in *every accessible*
   world yields a necessary fixed individual relative to that frame.
2. **Refuted as a general implication:** Shared root across populated histories
   plus even a tightly finite cause graph for dependents does **not** by
   itself yield a necessary individual.
3. **Model sensitivity:** Restricting away the empty extension can turn the
   same root from contingent to necessary without altering populated histories.
4. **Still open:** Which worlds genuinely are metaphysically possible? Can the
   empty extension be eliminated without assuming the desired conclusion?
   Does a universally quantified PSR, or a defended causal-powers principle,
   exclude this control? If a necessarily present root is secured, what
   further premises warrant its causal power, nonnaturalness, uniqueness,
   simplicity, or personhood?

The rooted model **does not satisfy unrestricted PSR**: the designated root
has no cause or separate supplied explanation. Its causal coverage pertains
only to present nonroots. This difference is a testable gap, not a philosophical
victory. An alternative that accepts brute roots and an alternative that
demands a necessary foundation should be compared as *complete theories*, not
by arbitrarily deleting an inconvenient world label.

### Connection to existing finite-to-infinite and PSR results

These controls connect to existing independent results and a worldwise-reason
model theorem, without conflating their vocabularies or silently transferring
their premises:

| Existing result | Exact contribution | Remaining step |
| --- | --- | --- |
| `CAUSAL-FINITE-LOCAL-WITHOUT-GLOBAL` | Every finite nonempty induced restriction of the infinite reverse-successor graph has a source, but the whole loop-free infinite graph has none. | No theorem promotes local sources to a global source without an added hypothesis. |
| `CAUSAL-FINITE-BRANCHING-TO-FINITE-ANCESTRY` | Finite immediate predecessors **and** well-foundedness yield finite total distinct ancestry. | Neither hypothesis is entailed by an observed finite prefix. |
| `PSR-WELL-FOUNDED-CAUSE-HAS-EXPLAINED-SOURCE` | At one inhabited world, an existence-PSR token and well-founded causes yield an existent with an explanation and no incoming existent cause. | No de-re necessity or genuinely sufficient metaphysical explanation follows. |
| `TruthCore.Modal.WorldwiseExplanation.worldwiseWithoutStable` | An explanation can exist in each world for a necessary individual without one rigid reason token across worlds. | Worldwise explanation does not entail cross-world explanatory identity. |

The *first* independence concerns **finite observations versus infinite causal
ancestry**. The new root fork concerns **a finite, well-ordered history versus
what holds across worlds**. The existing PSR and worldwise-explanation
controls concern **reason tokens versus sufficient grounds**, and **worldwise
existential witnesses versus rigid tokens**. Combining these results safely
requires explicit maps between the separate causal, modal and explanatory
models. Nothing from mathematical compactness or finite prefixes establishes
real causal history without an additional premise.

In particular, finite causal depth here prevents an objection that the new
countermodel secretly relies on an infinite regress. It still does not settle
the separate metaphysics of supertasks or an infinite past.

### Three explicit routes for the next composition

1. **Root from dependence (#487):** In an inhabited actual world with a
   well-founded same-world causal predecessor relation, impose the *additional*
   rule that every actually present contingent concrete individual has an
   actually present concrete predecessor. A predecessor-minimal actual
   concrete individual cannot then be contingent, and classical logic can
   turn the negation of its contingency into necessary presence. Unlike our
   root-presence bridge, this route seeks to **derive** necessity from a
   substantive dependence premise. It needs a separate proof with the exact
   `Contingent`, `Concrete` and well-foundedness semantics of #487. Its
   philosophical burden falls on that dependence rule, not on an unexplained
   deletion of the empty world.
2. **Empty profile from finite omissions (#484):** For closed admissible
   Boolean profiles, joint omission of each finite roster subset can force
   the empty profile into the admissible set. This points in the *opposite*
   direction: deny finite omission, deny closure, or admit the empty world.
   Neither finite-character closure nor metaphysical modal accessibility is
   established here.
3. **No necessary individual despite necessary population (#485):** The
   existing alternating countermodel leaves the possibility of a necessary
   existential disjunction with merely world-local witnesses. Its explanatory
   status is different from a fixed bearer or one stable reason token, and
   must be tested with explicit grounding/PSR bridges.

This is the reusable pattern behind the intersections:
`∀ finite subsystem, ∃ local source` does not imply a global source;
`∀ world, ∃ existent` does not imply one fixed existent;
`∀ world, ∃ reason` does not imply one rigid reason. The additional
shared-root and population assumptions in our theorem eliminate one of these
scope gaps without settling whether those assumptions are true of reality.

### Proof and acceptance

- Lean modules: `EmptyWorldFork.lean` and the three corresponding `Solution`
  theorems under `Results/Case/Catholicism/StageOne/NecessaryIndividual`.
- Corpora: one independent statement, inference, argument and result per
  theorem; exact definitions and disambiguation, plus comparator contracts.
- The current stage is a mathematical result proposal until `lake build`,
  `corpus.py bind-check`, and `verify-result` have run successfully. A green
  metadata check alone is insufficient.

Intended root-path open-premise change: **none**. This investigation makes an
implicit modal-domain choice visible, not a new established theological root
conclusion. Its open philosophy premises are genuine epistemic-frontier work.
