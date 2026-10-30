# What each stronger PSR adds (#755)

This note maps PSR formulations in one arena and says what each step costs. The
theorems are `collapseCore` and `strengthMap` in
`TruthCore.Results.Explanation.PSRStrength.Solution`, over the vocabulary of
`TruthCore.Explanation.PSRStrength`. Both are zero-axiom. They establish conditional
consequence and the satisfiability of encoded bundles. They do not establish any PSR,
the metaphysical possibility of any model, or any premise on a root route.

No source claim is added. Pruss, Koons, Gale–Pruss, Leibniz, van Inwagen and Oppy
(#409, #365) were not read for this work, so no row below is attributed to them.
"BCCF" and "weak PSR" name formal conditions here, not those authors' exact theses.

## The relation being compared

`Arena.explains w r f` reads: at world `w`, the fact `r` is admitted as a reason why
the fact `f` obtains.

- **Ordinary language.** "The kettle boiled because the burner was on." A reason is
  a fact offered in answer to "why this?".
- **Examples and counterexamples.** Reasons that do not necessitate: an agent's motive
  for a free choice, or a stochastic setup for its outcome, on views that count them
  as explaining. Modal entailment that does not explain: `f` entails itself, and the
  `copy` model shows that this satisfies `FactPSR`, and so `ContingentPSR` and `NoBrute`
  (`ExistencePSR` needs `Coherent` as well, and weak PSR needs reflexivity).
- **Not the same as.** Efficient causation (`Ontic.Causes`, see
  `DISAMB-PSR-EXPLANATION-CAUSE`), modal sufficiency (`Necessitating`, see
  `DISAMB-PSR-REASON-NECESSITATING`), and conjunct-hood (`conjunct`).
- **Structural properties.** None is assumed. Transitivity, asymmetry and
  well-foundedness are absent. Factivity, necessitation, independence, distribution and
  contingent irreflexivity are separately named hypotheses, because which of them
  explanation has is the point at issue.
- **Generalization.** The map does not generalize from ordinary explanation to a
  metaphysical law. Each formulation is a hypothesis under test.
- **Competing accounts.** Humean or brute-fact views deny coverage; the necessitarian
  reading adds `Necessitating`; the nonnecessitating libertarian reading keeps coverage
  and rejects it. All three have a row below. Unificationist and contrastive accounts
  have no row: see the open axes.

## The incompatible core

`collapseCore` certifies that, given `ConjunctSound`, these seven members cannot all
hold at a world: `NoBrute`, `Factive`, `Necessitating`, `Distribution`,
`IrreflexiveContingent`, an aggregate `BCCFAt`, and a `Contingent` truth. Each member
is deleted by a model keeping the conjunct law and the other six, so the bundle is
inclusion-minimal. That is not minimum cardinality, and the core forces no choice of
which member to reject.

| Deleted member | Model | What survives |
| --- | --- | --- |
| Coverage (`NoBrute`) | `bruteTerminus` | A contingent terminus with no reason |
| `Factive` | `falseToken` | A reason token that is never true |
| `Necessitating` | `ground true` | A necessary ground with a nonnecessitating reason for a contingent fact |
| `BCCFAt` | `cofinite` | Unrestricted fact coverage, no aggregate of all contingent truths |
| `Distribution` | `mutualReasons` | A fact and its aggregate, each the other's reason |
| `IrreflexiveContingent` | `selfWhole` | A contingent fact that is its own reason |
| `Contingent` | `allNecessary` | No contingency at all |

A second bundle replaces distribution and irreflexivity with `ReasonIndependent`. It
is also inconsistent; `collapseCore` does not certify that this second bundle is
minimal.

## The strength table

Each row is a clause of `strengthMap`. "Bridge" is the extra hypothesis the valid edge
uses. World-relative formulations are read at the named world.

| Tested edge | Result | Bridge or separating model |
| --- | --- | --- |
| `FactPSR` → `ContingentPSR` | valid | none |
| `FactPSR` → `ExistencePSR` | valid | `Coherent` |
| `ContingentPSR` → `NoBrute` | valid | none |
| `ContingentPSR` → `ExistencePSR` | invalid | `ground false`: the necessary ground has no reason |
| `ExistencePSR` → `ContingentPSR` | invalid | `existenceOnly`: a contingent event has no reason |
| each member explained → whole explained | invalid | `history false`, every quality clause retained |
| whole explained → `ContingentPSR` | invalid | `history true`: the contingent law has no reason |
| each member explained → one `CommonReason` | invalid | `history` at `lawful` has none; `ground true` has one. Full `ContingentPSR` without a common reason is not tested |
| `NecessaryPSR` → `ContingentPSR` | valid with reflexivity | fails in `nonReflexiveBare` |
| `ContingentPSR` → `WeakPSR` | valid with reflexivity | fails in `nonReflexive` |
| `ContingentPSR` → `NecessaryPSR` | invalid | `modalGap` at `some true` |
| `WeakPSR` → `NoBrute` | valid | `Distribution` and `UnexplainedFacts`; dropping either fails (`modalGap`, `modalGapDiagonal`) |
| `StableReason` → reason at every world where true | valid | none |
| reason at every world → `StableReason` | invalid | `shiftingReason` (`□∃r` is not `∃r□`) |
| `LocalCausalPrinciple` and `ExternalCause` → `ExistencePSR` or `ContingentPSR` | invalid | `causeOnly`: an infinite causal chain, no reason |
| `ExistencePSR` and `LocalCausalPrinciple` → `ExternalCause` | invalid | `ground true` |
| `FactPSR` → `ReasonIndependent` | invalid where contingency exists | `copy A` has `FactPSR`, `Necessitating`, `Factive` over any `A` |
| `ReasonIndependent` → `Necessitating` | invalid | `ground true` |

The formulations are not linearly ordered: `ContingentPSR` and `ExistencePSR` are
incomparable, and quality conditions are a separate axis from scope.

## What a stronger version buys

- **Extending scope to necessary facts** adds a demand on necessary individuals,
  which `ground false` fails while meeting `ContingentPSR`.
- **Adding a whole** is not a further application of member coverage. `history false`
  explains every member and not the whole. To reach the whole, a domain must contain
  an aggregate; `cofinite` shows that fact coverage alone does not supply one.
- **Adding necessitation** is the step that makes contingency collapse a threat. In an
  extensional domain with entailment conjuncts (`Extensional`, `EntailmentConjunct`),
  weak PSR with factive, necessitating, distributing, irreflexive reasons excludes
  contingency at the world. The same domain without necessitation admits contingency,
  an aggregate and unrestricted coverage together (`extensionalGround`).
- **Weakening to possibility** avoids collapse only if a bridge is refused. Weak PSR
  yields `NoBrute` given distribution and diagonal facts, and extensional domains
  supply the diagonal facts and an aggregate. So the weak version's safety depends on
  rejecting extensionality or a reason quality, not on its modal position alone.
- **Requiring independence** is what separates a real reason from `copy`, which meets
  `FactPSR` over any arena. It is a quality condition, not more scope.

## Controls

Positive: `ground true` is a necessary ground with a nonnecessitating reason for a
contingent fact. The signature has no predicate for personal agency, so necessary
personal ground with free choice and necessary impersonal ground with an
indeterministic output are the same structure here, and no theorem separates them.
`history true` is an infinite history with a law as necessitating independent reason
for the whole; the law is itself contingent and unexplained there.

Negative: `bruteTerminus` is a brute contingent terminus. `history false` is a locally
explained, globally unexplained infinite chain.

## Surviving configurations

| Configuration | Survives | Smallest listed premise that eliminates it |
| --- | --- | --- |
| Brute contingent terminus | `ContingentPSR` fails, the rest of the core holds | `NoBrute` |
| Unexplained infinite history | member coverage | a reason for the whole, then `NoBrute` for the law |
| Lawful history with brute law | a reason for the whole | `NoBrute` for the law |
| Necessary ground, nonnecessitating reason | `NoBrute`, `ExistencePSR` | `Necessitating`, with the rest of the core |
| Domain with no totality | `FactPSR`, all qualities | a premise that an aggregate fact exists |
| Necessitarian, no contingency | the whole core except contingency | any contingent truth |

Coverage here favors no worldview. Theism's nonnecessitating ground and the impersonal
ground have the same row, and each theorem leaves its conclusion conditional.

## Open bridges and axes

- **Open bridges:** whether explanation is necessitating, whether a totality fact
  exists (`BCCFAt`), `Distribution`, `UnexplainedFacts`, and extensionality. Nothing
  here defends or refutes any of them.
- **Axes not formalized:** the rational-inquiry norm (axis 1 of #755), contrastive
  explanation, probabilistic explanation, and independently productive `Supply`
  (#698, #750). `ReasonIndependent` is modal only, so a reason that merely differs
  modally from its target passes it without being relevant to it.
- **Not composed:** #465's modal countermodels, #735/#750 adequacy and #746 stopping
  are not imported as lemmas. Only #312's `ExistencePSR` and `ContingentPSR` are
  composed, along `ofModel`.
