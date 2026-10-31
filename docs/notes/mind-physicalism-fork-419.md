# Mind and physicalism: a certified fork and an incompatible core (#419)

The arena is one frame (`TruthCore/Alternatives/MindPhysicalism.lean`): occurrences
that instantiate kinds, a target mental kind, physical kinds, and primitive `Causes`
and `RealizedBy`. Lean checks consequence only. All premises stay open, and every
model below is a finite formal interpretation, not a rival theory or a possibility claim.

## Source reading

Read from `PAPINEAU-RISE-PHYSICALISM-3-12`, pp.8-12, and notes 5-6 in
`PAPINEAU-RISE-PHYSICALISM-13-33`. The causal argument is at p.9. Its three exits are
at pp.10-11 and a generous reading of causation gives realization (p.11).

Premise 3, "The physical effects of mental causes are not all overdetermined", has
two readings, each with its own claim. Per cause, it yields a universal
conclusion in identity-or-realization form. Taken collectively it does not (`collectiveHybrid`). That is a result
about the reading: Papineau says the argument "seems pretty clearly valid" (p.10), and note 6 only discusses
Sturgeon's separate equivocation charge, which is not formalized here.

Not consulted, so nothing is attributed: any eliminativist or nonreductivist author.
Those labels are the Lean definitions below. Papineau does not address q.75.

## Results

| Theorem | Exact content |
| --- | --- |
| `physicalistFork` | Excluded middle, completeness, influence, distributive premise 3 ⊢ `Eliminative ∨ Reductive ∨ Nonreductive` |
| `fourWayCoverage` | Excluded middle ⊢ `PhysicalistFork ∨ SomeUnbased`; no causal content |
| `positionsExclusive` | The six pairs among the four positions are incompatible, in every frame |
| `noPerSeOperation` | Those four premises, tokening and basis/sharing ⊢ no per-se operation |
| `q75BundleIncompatible` | Five q.75 premises with those six ⊢ `False` |
| `someBased` | Excluded middle, completeness, collective premise 3 ⊢ some target occurrence is based |

Witnesses, each with the causal premises: `eliminativeWitness`, `reductiveWitness`,
`realizationWitness` (a mental occurrence with no physical kind),
`occurrenceIdentityWitness` (all mental occurrences physical, the kind not).

Deletion models, each keeping a per-se operation and the other premises:
`completenessExit`, `influenceExit`, `overdeterminationExit` (each also with an
unbased occurrence and the fork false), `tokeningExit` and `bridgeExit` (each with
the reductive condition). So the core is inclusion-minimal for its five non-logical
premises. No model omits excluded middle. `bundleWitness` shows the premises jointly
satisfiable, so `noPerSeOperation` is not vacuous.

## What this does and does not show

Physicalism is not refuted and is not established. `physicalistFork` says what
follows given the premises; the exits say what an account with an unbased occurrence
must deny in that model. The core forces rejecting some member and selects none.

The decisive open bridge is `STMT-PHYSICAL-BASIS-IS-BODY-SHARING`. Q.75 a.2 speaks of
the body sharing in an exercise. Papineau speaks of identity or realization. Under
`bridgeExit` a reductive frame and a per-se operation coexist, so q.75's conclusion
and the causal argument touch only through that bridge. Whoever asserts it owes a
reading of `BodyShares` on which a realized exercise is shared with the body, and
that reading must then be checked against the q.75 interference premises. Whoever
denies it owes an account of what `PerSeIntellectualOperation` then excludes.

## Semantic grounding

`Causes` follows ordinary usage (a decision causing an arm movement, not a mere
correlate) and is not given transitivity, asymmetry or well-foundedness, since no
theorem needs them. `RealizedBy` relates a role state to its filler (a program step
and a circuit event, not that event's later effect); it differs from causation by
holding between an occurrence and what fills its role, and is given no structural
law. Generalizing either from ordinary cases to intellectual exercise is exactly what
the open premises assert. Rival accounts (Davidson's particulars, subset or
mechanistic realization) are not adjudicated, and a particulars reading needs another
frame. Overdetermination here means a distinct cause in Papineau's p.10 sense; a
noncompeting cause that is neither among nor realized by the physical determiners
counts as overdetermining, so a reply from noncompetition rejects premise 3 here.

## Remaining gaps

- Every premise, including tokening, the bridge and Papineau's completeness.
- A pinned eliminativist or nonreductivist witness, and hylomorphist, dualist,
  idealist and neutral-monist replies; no branch is identified with these.
- The q.75 interference premises (`docs/human-intellect-rival-assessment.md`).
- Consciousness, intentionality and rational agency, which stay separate.
- No inference toward theism or Catholicism is made, and no root premise changes.
