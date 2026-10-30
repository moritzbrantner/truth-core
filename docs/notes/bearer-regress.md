# Bearer regress: terminus, cycle or endless support (#562)

Results: `BEARER-OUTCOME-COVERAGE`, `BEARER-PRIMARY-SUBSTANCE-TERMINUS`,
`BEARER-REGRESS-CONTROLS`. Module: `TruthCore/Causality/BearerRegress.lean`.
All premises other than the sourced Categories reading are analyst premises;
none is attributed to a source and none is established.

## The relation used

Direct existential support (`PresentEsseSupport`, `DEF-PRESENT-ESSE-SUPPORT`) is
reused, not reinterpreted. For this investigation it is read as follows.

- **Ordinary meaning.** `c` exists and `x`'s existence directly relies on `c`:
  a smile on a face, a wave in water, on the reading that the second cannot be
  there without the first.
- **Contrast.** Bearing is attribution of an act to a subject. Being in a subject
  is the Categories relation: present not as a part and unable to be apart
  (I.2, within 1a20-1b9, read in the materialized `ARIST-CAT-V`). Explanation is a further
  relation. A cause that produced something and has ceased is a counterexample to
  reading production as support at that world.
- **Structural properties.** Transitivity is not assumed of the direct relation;
  the ancestry closes it. Well-foundedness is not assumed by the coverage result.
  It is an open premise of the primary-substance result, with no defense given
  here: experience of dependent things does not show that the relation has no
  cycle or endless descent in general.

## Rivals and the models

| Rival | Model | What the model shows |
| --- | --- | --- |
| Primary substance as bearer | `SubstanceBranchModel` | The form is satisfiable with well-founded support. |
| Fundamental event or process | `NonSubstanceBranchModel` | A well-founded terminus can fail the supplied `Substance`, and its bearer need have no bearer. Nothing in the model marks it as a process. |
| Bundle or trope complex | `BundleCycleModel` | Mutual support among members is compatible with nothing bearing the bundle. Unity of the bundle is not addressed. |
| Cyclic support | `CycleBranchModel` | Satisfiable with every entity dependent. |
| Infinite descending support | `ChainBranchModel` | Satisfiable with no cycle and every entity dependent. |

These show that the encoding is satisfiable, not that any rival is adequate or
possible. A nihilist's simples are not separately modelled.

## Findings

1. **The regress step is not free.** No theorem passes from "has a bearer" to "its
   bearer has a bearer"; the ancestry runs through support alone.
2. **Coverage needs a premise and is classical.** `someBearerOutcome` uses
   excluded middle as a hypothesis, and without `BearerAncestryDependentsSupported`
   a dependent bearer can have no terminus in the nondependent sense
   (`OmitAncestryPremiseModel`). That premise makes the nondependence of a terminus
   a contraposition: it adds a constraint only because `Dependent` is primitive.
3. **The exclusive split is accessibility, not "has a terminus".** One ancestry can
   have a terminus and a cycle (`TerminusWithCycleModel`), and termini on both
   sides of `Substance` (`BothTerminiModel`).
4. **From terminus to Categories test takes two bridges.** Neither is attributed to
   Aristotle, and each omission model leaves no terminus passing the test. The
   said-of bridge is especially disputable, since it has an individual directly
   supporting what is said of it.
5. **The negative test does not settle kind.** A terminus can pass it because nothing
   is in or said of anything, and fail a separately supplied `Substance`
   (`NegativeTestControl`). The 2a11-14 examples, an individual human or horse, are
   not part of the formal reading. Excluding a primitive-process rival needs a
   further premise, which would have to be defended against that rival.
6. **A terminus is not necessary.** It can be contingent (`ContingentTerminusModel`).

## Open

Defending well-foundedness for this relation; a bridge from a terminus failing
`Substance` to a process; a constructive coverage; omission models for occurrence,
the bearer principle and bearer existence; composition with #326 nihilism and #330
hylomorphism.
