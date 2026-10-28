# Scientific testing, auxiliary trust and calibration

This bounded science comparison contributes to #247/#363 and the owner's
foundational investigation. Its question is what a failed or successful
physical test can establish about a disputed hypothesis when instrumentation
and other assumptions also enter its prediction and interpretation. It adds
no root route and discharges no philosophical premise.

## Actual witness and reading boundary

Consulted Pierre Duhem, *La Théorie physique. Son objet et sa structure*,
Paris: Chevalier & Rivière, 1906, seconde partie, chapitre VI, printed
pp.295–359. `DUHEM-THEORIE-PHYSIQUE-VI` pins Wikisource revision 11940991:

<https://fr.wikisource.org/w/index.php?title=La_Th%C3%A9orie_physique/SECONDE_PARTIE/Chapitre_VI&oldid=11940991>.

Two actual fetches matched raw SHA256
`5a50d085adb9d0a7d643c444e2b410fa716c62769265a60a983d56971e7ac827`
and normalized chapter text SHA256
`47b975f671592ae856ebb7931abde33feb90b05cdeb0ec3fdcdd4af4190d6c19`.
The full chapter is materialized for context; the bounded source readings
concern §§I–III, pp.295–312, and §X, pp.356–359. These selected sections and
immediate context were read in the verified French. The intervening detailed
Newtonian/electrodynamic arguments are not claimed as exhaustively processed
or as independent results of this batch. No English translation is relied on.
Only locators, hashes, short incipit and paraphrases are committed.

A revision URL still transcludes scanned-page transcriptions; its immutable
revision identifier does not by itself freeze every embedded page. The byte
and text hashes identify the actual consulted response, and later drift must
fail. A bounded CDX query for the chapter's canonical URL returned an empty
list; a save request returned HTTP 523. No verified archive fallback is claimed.
The snapshot therefore remains availability-fragile. One sentence in the
transcribed Foucault vignette in §III repeats *ondulations* across opposite
experimental outcomes. No physical sign inference or claim about the correct
historical light theory relies on that sentence: the ensuing bundle and
exhaustiveness argument is the consulted claim context. This transcription
concern is preserved rather than silently repaired or made into a contradiction
in Duhem's theory.

## Argument and source scope

1. **§I, especially pp.299–301:** a physicist uses a schematic theoretical
   apparatus when setting up and interpreting the concrete instrument. The
   opening of the section places physical theory's task in representing and
   classifying experimental laws. This is a positive account of scientific
   practice, not the thesis that no observation is possible.
2. **§II, pp.301–302:** using accepted theory to solve an application problem
   differs from testing that theory. Measuring an accumulator for a lamp does
   not by itself add an independent test of the whole theory. Duhem explicitly
   denies that theory use in such an application is itself a logical fault.
3. **§II, pp.303–307:** a forecast and the interpretation of its failure use
   more than the disputed hypothesis. The mismatch implicates their ensemble;
   locating the error in one member retains trust in the rest. Duhem's Wiener
   example permits a repair of another optical assumption. This is an argument
   against automatic isolated fault attribution, not a proof that every
   conceivable auxiliary repair is credible or that rational rejection is
   impossible.
4. **§III, pp.308–312:** temporarily grant that all other assumptions are
   secured. A second gap remains: the two considered physical alternatives
   may not be a logically exhaustive contradictory pair. Rejecting one then
   does not yield incontestable truth of the other. This distinguishes a
   checked exhaustive fork under a specified background from an unproved
   claim to have listed every physically admissible alternative.
5. **§X, pp.356–359:** logic does not dictate the unique repair. A physicist
   may reasonably prefer a modest correction or a simpler replacement using
   *bon sens*. Duhem does not grant all consistent repairs equal merit; he
   emphasizes defeasible judgment and impartiality. He also expresses optimism
   that prolonged disagreement will end. This batch does not turn that
   optimism into a proved convergence/reliability theorem.

Five independent prose statements/claims record these readings. None is
presented as a mechanically established empirical or epistemic fact. Duhem is
not credited with the additive model below.

## Checked mathematical target: an instrumental auxiliary made explicit

An analyst profile consists of a signal function `f : X → V` and one constant
additive bias `b : V`, with `V` any additive commutative group. Its reading at
`x` is `f(x)+b`. `SameReadings f g b c` means exact agreement at **every** input.
The certificate in `TruthCore.Results.Science.MeasurementCalibration.certificate`
has four clauses:

- Complete reading agreement holds iff some constant `d` satisfies
  `g(x)=f(x)+d` at every input and `c=b−d`. This is all-input
  nonidentifiability, not merely underdetermination after finitely many tests.
- Supply an actual input `x₀`, a reference value `k`, and the two equalities
  `f(x₀)=k` and `g(x₀)=k`. Among same-readings constant-bias profiles, the
  biases and all signal values then agree. The type supplies these equalities;
  it does **not** certify their truth about a real standard, independent
  discovery or warrant for believing them.
- A Unit/Int witness gives signal 0 with bias 1 and signal 1 with bias 0.
  Every reading equals 1, although the signals and biases differ. This is an
  explicitly inhabited, single-input omission witness; the general theorem,
  rather than this one fixture, quantifies over arbitrary input carriers and
  signal functions.
- A separate Boolean/Int profile permits input-dependent bias. The profiles
  have all readings 0 and the same signal at `false`, yet different signals
  at `true`. One anchor consequently does not identify the enlarged class.

The last clause is a changed semantic profile, not a counterexample to the
constant-bias theorem. The group laws, additivity, exact response equality and
constant bias are mathematical restrictions. Actual instrument drift,
noise, nonlinear response, calibration independence and empirical applicability
remain open. Identifying a mathematical profile is not an explanation of why
its signal, instrument or laws obtain.

The Challenge was written before proof development and remains unchanged.
The Solution uses standard Mathlib group cancellation and `abel`, not an
unproved physical or epistemic assumption. Development diagnostics accepted
full combined vocabulary/proof content (imports hoisted, local module import
replaced by its exact contents) at shared preview revision
`f2544a0142304bf074112e7323cb5b8ab6e46840`, content SHA256
`347076826149d3cd925da7d575968c696878ce055746e368ec77cf0b70e9eeba`.
The response had no errors/warnings; its informational axiom print lists only
`propext`, within the approved Mathlib policy. The first attempt exposed one
closed-decision normalization issue in the integer fixture, repaired without
changing the Challenge or certificate. Final canonical module build, binding,
Comparator and NanoDa remain CI obligations.

## Reuse and why this is a different constraint

Dossiers inspected: `STMT-HUME-INDUCTION-TESTS`,
`STMT-SCIENCE-PREDICATE-RECODING`, and
`STMT-HISTORY-CONTRASTIVE-CONTROLS`.

- `TruthCore.Results.Modern.Hume.Induction.checks` already gives finite
  prediction/intervention counterhistories and explicitly scoped normative
  bridges. Another delayed-failure sequence would be redundant.
- `TruthCore.Results.Science.PredicateRecoding.controls` already separates
  value-preserving recoding from phase independence in a fixed basis. It does
  not isolate an unknown signal from a jointly adjusted instrumental bias.
- `TruthCore.Results.Modal.HistoryContrastive.controls` already separates
  local coverage and discrimination from sufficient ontological explanation.
  A calibration success is not silently upgraded to that stronger task.

The new algebraic constraint applies even when **all** response inputs are
supplied and states exactly what a common anchor adds under the constant-bias
restriction. Additive cancellation is analogous to other compensation and
translation controls, but sensor bias is not desire polarity or spatial
identity. No new generic group-action infrastructure or identity relation is
introduced. An opaque `T ∧ A → O`, `¬O` modus-tollens certificate was rejected:
it would transcribe an inference without exposing this internal structure.

## Strongest rival replies on common questions

The table compares explicit replies to the same bounded task; entries are
not aggregate scores or declarations that a worldview has won. The last two
rows are live analytical alternatives, not new historical attributions to
Popper, a generic realist, or all instrumentalists.

| Task | Duhemian bundle/good-sense account | Selective realist reply | Instrumentalist/pragmatic reply |
|---|---|---|---|
| What supplies predictions? | A theoretical ensemble including instrumental interpretation | Target theory plus separately supported measurement/auxiliary models | A usable predictive representation with declared operating limits |
| What does a failed test show? | At least part of the used ensemble requires revision | Against a target conditionally on independently supported auxiliaries and reliable observation | The representation fails in the tested application/domain |
| How select the faulty part or repair? | Good-sense judgment informed by experience and impartiality | Independent calibration, alternative instruments, intervention, cross-checking and explanatory integration can constrain repairs | Prefer repairs that improve reliable use, simplicity or coverage in the declared task |
| Does success establish unique theory truth? | No deduction without a secured ensemble and exhaustive alternatives | May support a fallible claim of truth; uniqueness requires additional defenses | Success may justify use without asserting unobservable ontology |
| What remains open? | Reliability and discrimination of good-sense judgments, actual ensemble correctness | Independence/reliability of calibration and observation, admissible-alternative scope, move from success to truth | Adequacy of pragmatic aims and any stronger ontological claim |

A realist need not demand certainty or deny theory-ladenness. Independent
cross-checks need not presuppose the disputed target in the same way; whether
particular checks do so is a further investigation. Conversely, calling an
auxiliary independent does not prove it reliable. An instrumentalist can offer
an affirmative predictive/practical account without answering why a complete
world exists. A holistic account may treat evidential mutual support as rational;
it still owes a non-arbitrary criterion, rather than inheriting warrant merely
from a graph cycle.

## Connection to regress and the larger case

Sextus's establishment challenge, an infinitist's available reasons,
Duhem's practical/critical experiment and Leibniz's why-this-world question
are not identical adequacy demands. Uncertainty in auxiliary selection does
not prove every scientific premise dogmatic or every theory unwarranted.
Equally, empirical success alone does not discharge the existence/grounding
premises of the Catholic case. The Catholic account owes the same clarity about
its auxiliary metaphysical commitments and explanatory standards; it gets no
certainty merely from identifying a preferred conclusion.

Intended and actual root-route premise delta: **none**. The five source claims
remain philosophical commitments, and the new result proves only a mathematical
conditional/model-class boundary. No source proposition is promoted to an
established root premise, no metaphysical alternative is declared impossible,
and no full science or positivism campaign is closed. Next decisive task is
`SCIENTIFIC-AUXILIARY-ADEQUACY`: defend a particular anchor/profile and its
reliability, or defend a different adequate empirical-choice standard, before
claiming an actual scientific or metaphysical identification.
