# D: serial accessibility and non-vacuous collapse

Issue #263 studies D using the shared fixture from #261. Every world has at
least one accessible successor (`Serial`). Reflexivity, symmetry and transitivity
are separate conditions. These are stipulated mathematical models. They establish
neither metaphysical possibility nor an unrestricted conceivability bridge, and
are not a refutation of Hume's actual argument.

The vocabulary is unchanged: `Frame`, `Formula`, `Holds`, `Box`, `Dia`,
`ResearchFixture.MC`, `allPredicates`, `expressible`, and the existing `Contingent`.
For a fixed root `w` and proposition domain `D`, keep these distinct:

- Actual collapse: `MC F D w`.
- Possible collapse: `Dia F (MC F D) w`.
- Necessary collapse: `Box F (MC F D) w`.
- Possibility implies actuality for a predicate: `Dia F P w → P w`.
- Contingency at that same root: `Dia F P w ∧ Dia F (fun v => ¬ P v) w`.

No root is changed when moving between these expressions. In particular, possible
collapse witnesses collapse at a successor, not at the actual root. No `C(MC)`
or `C(MC) → Dia MC` premise is introduced.

## What seriality proves

`MODAL-D-LAWS` proves five general clauses, with every assumption quantified in
`DResearch.LawChecks`:

| Conclusion | Exact additional assumptions |
| --- | --- |
| An MC world accesses itself | Seriality, MC, and admissibility of its identity predicate |
| Full MC iff the successor set is exactly the nonempty singleton `{w}` | Seriality; all predicates |
| The restricted-domain MC world accesses itself | Seriality, MC, excluded middle, negation closure, and world propositional extensionality |
| A true admissible predicate at an MC world is possible | Seriality, MC, domain admission, actual predicate truth |
| Necessary MC implies possible MC; `Box False` fails | Seriality only; same frame/domain/root |
| Actual full MC excludes contingency | Full MC; no seriality assumption needed because contingency already supplies successors |

The proof composes the shared identity-separation and extensional-separation
lemmas with a successor supplied by seriality. Conversely, if every accessible
world is the root, every predicate true there persists. The extensionality route
keeps excluded middle as a hypothesis; the proof uses none of Lean's classical
axioms. It is not a claim that every route to restricted-domain identity needs
excluded middle.

Seriality removes empty-successor vacuity and, with full predicates, forces an
MC world's self-loop. It does not propagate collapse from a successor to the
root, connect disconnected components, or identify every world in the carrier.
`MODAL-D-SCOPES` also reuses the shared K sink: full MC holds vacuously there,
but self-access and seriality fail. Thus the self-access conclusion genuinely
changes when seriality is removed. The restricted two-cycle below shows why
identity-predicate admissibility cannot be silently dropped.

## Reproduced finite witnesses

All carriers are explicitly enumerated constructor types. Every edge and atomic
truth value is listed, including false entries, and carrier completeness is
proved. The numerals below are local names for those constructors, not a new
identity criterion. `MODAL-D-COUNTERMODELS` checks the following frames.

| Pocket world | Accessible worlds | Unit atom |
| --- | --- | --- |
| 0: root | 1, 2 | false |
| 1: collapsed pocket | 1 | true |
| 2: left | 3 | false |
| 3: right | 2 | false |
| 4: disconnected alternative | 4 | false |

Pocket is serial, non-reflexive, non-symmetric and non-transitive. Worlds 2 and 3
form a closed two-cycle. World 4 is a separate self-loop, inaccessible from the
root. Both 1 and 4 have full MC. At root 0, full MC is false, possible full MC is
true, and necessary full MC is false: successor 2 does not have full MC. Hence
seriality and `Dia MC` do not imply actual MC or exclude contingency.

| Fork world | Accessible worlds | Unit atom |
| --- | --- | --- |
| 0: root | 1, 2 | false |
| 1: left | 1 | true |
| 2: right | 2 | false |

Fork is serial, non-reflexive and non-symmetric. Its two endpoints have full MC,
so root 0 has **both possible and necessary full MC**, but not actual MC. This
three-world witness shows that even `Box MC` does not yield root MC in D.

In both frames take `P(w) := w = 1`. The witness for `Dia P` is 1 and for
`Dia (not P)` is 2, at the common root 0. These are independently constructed from
the edge/truth tables; no collapse premise supplies them. Moreover, `P(0)` is
false, so `Dia P → P` fails. The reports list exactly `[1]` as atom witnesses and
`[2]` as counterexamples to its necessity at root 0. These are semantic
counterexamples, not empirical evidence of real-world contingency. In each
collapsed endpoint, its only successor is itself; full MC there therefore does
not extend its conclusions to other components or to the root.

## Fixed-language scope and optional extensionality

`MODAL-D-LANGUAGE` uses the smallest non-reflexive serial cycle:

| World | Accessible worlds | Unit atom |
| --- | --- | --- |
| false | true | true |
| true | false | true |

Structural induction proves that **every** formula in the fixed Unit language
has the same truth at both labels, including formulas with box and diamond.
Language-relative MC holds at both worlds, although neither world accesses itself.
Possible and necessary language MC hold at `false`. Full MC fails at both worlds:
the full domain admits the identity predicate distinguishing them. That predicate
is not expressible in the fixed language. The language is negation-closed but its
world-extensionality condition fails; no theorem identifies the two labels. If
world extensionality, negation closure and excluded middle were supplied, the
restricted identity law would rule out this non-reflexive MC case.

No fixed-language formula is contingent at the root of this cycle, because it
has only one successor. Nonetheless the extended predicate `w = true` witnesses
possible truth without actual truth at `false`. Thus a claim restricted to fixed
formulas is not silently promoted to one about every predicate.

`MODAL-D-SCOPES` compares domains while keeping each frame and valuation fixed:

| Root 0 | Actual full MC | Possible full MC | Necessary full MC | Actual language MC | Possible language MC | Necessary language MC |
| --- | --- | --- | --- | --- | --- | --- |
| Pocket | false | true | false | false | true | true |
| Fork | false | true | true | false | true | true |

The negated atom refutes actual language MC at both roots. In Pocket, formulas
agree at worlds 2 and 3 by structural induction; they cannot expose that cycle's
failure of full MC. Both root successors therefore have language MC. Changing
only the proposition domain changes the truth of necessary MC at Pocket's root.
The full-versus-language comparison is not a change to the frame or actual root.

## Verification and interpretation boundary

Each row is part of one of four frozen Challenge/Solution contracts:
`MODAL-D-LAWS`, `MODAL-D-COUNTERMODELS`, `MODAL-D-LANGUAGE`, `MODAL-D-SCOPES`.
The first is proved from explicitly quantified frame/domain conditions, the
second by complete finite cases and identity separation, the third by formula
induction and constructor distinctness, and the fourth composes the earlier
endpoint results through domain restriction plus a separate cycle induction.
No contract merely applies an opaque bridge premise. No contract closes a
Catholic-case frontier premise or attributes a modal system to Hume.

Definitions link seriality, root truth, modal operators, domains, collapse,
identity admissibility, extensionality, contingency and each concrete frame.
The scope disambiguations keep actual/possible/necessary collapse, predicate
quantification, language agreement and world identity separate. No source claim
is added: these are mathematical experiments. Formal success cannot decide
whether this frame or proposition domain faithfully represents metaphysics or
what Hume meant by conceivability.

Reproduce the deterministic finite report and verify the results with:

```bash
lake build
lake env lean --run scripts/modal-d.lean
scripts/verify-result.sh MODAL-D-LAWS
scripts/verify-result.sh MODAL-D-COUNTERMODELS
scripts/verify-result.sh MODAL-D-LANGUAGE
scripts/verify-result.sh MODAL-D-SCOPES
```

Each report row is `(world, [(target, accessible), ...], atom, box(atom),
diamond(atom), atom witnesses, box(atom) counterexamples)`. Full MC is proved by
quantification over predicates; the report does not pretend to enumerate every
Prop-valued function. Build-time guards additionally exercise the root atom,
its possibility and contrary possibility. Permitted axiom lists remain empty.
