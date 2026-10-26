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

### Connection to finite-to-infinite and compactness work

These finite controls isolate the modal premise; they do not prove a ban on
infinite regress or a compactness theorem. A separate research lane can
formulate finite satisfiability of progressively longer acyclic causal
prefixes, ask whether an infinite completion satisfies their local clauses,
and compare that construction to well-foundedness and causal finitism. Any
step from mathematical compactness or finite prefixes to real causal history
must state a bridge premise. Finite causal depth here rules out explaining
away the countermodel *by invoking an infinite regress*; it does not settle
the separate metaphysics of supertasks or an infinite past.

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
