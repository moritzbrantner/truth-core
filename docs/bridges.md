# Bridges between components

Issue #401 asks for one growing root-connected graph. A *bridge* is an
inference between statements that sit in different inference components: the
same proposition read in two sources, one implying the other given established
statements, or two vocabularies for one concept. Bridges never merge statement
IDs (invariant 6). Each is a result with an inference, an argument, a frozen
Challenge, a Solution and a Comparator config under
`TruthCore/Results/Bridges/`; new vocabulary, if any, lives in
`TruthCore/Bridges/`.

A bridge connects statements; it does not by itself defend its premises.
Structured `transcription` fields distinguish instantiations and assembly from
non-transcription derivations. A transcription closes its conclusion only when
all its premises are already closed (invariant 16). A non-transcription bridge
can relocate an open obligation to another source reading, without establishing
that reading's fidelity or truth. The frontier reports these distinctions.

## Measuring

Components are the connected components of the undirected graph whose edges
join each inference's inputs, assumptions and discharged statements to its
output. The giant component is the one that contains `STMT-CATHOLICISM-TRUE`.

## Batch 1 (#401)

Fourteen bridge results and one new statement
(`STMT-EVERY-BEING-HAS-FINITE-PER-SE-PATH-TO-UNCAUSED`).

The batch adds one statement and fourteen results. Against the merged-main
baseline used for this repair (`993f4328`), the inference graph has 1172 → 1156
components, 1055 → 1042 singletons, and a root-containing component of
243 → 270 statements. These are connectivity measures, not frontier closure.

**Premise comparison: no philosophical premise is discharged.** The two
Aristotle analyses give the existing Aquinas potency consequences under the
stated analysis premises. The stage-4 connection is a transcription: neither
pilot cell, nor their conjunction, is closed. In particular, no source reading
is created for the bare historical commitment `STMT-PILOT-ROSE`.

`frontier --routes` leaves all eight route costs unchanged: skeleton 28,
quarta via 29, prima via 33, full description 35, maxime ens 36, classical
attributes 36, designated efficient regress 37, and q11 uniqueness 38. The
cheapest routes can continue to use the existing sourced commitments rather
than the longer bridge alternatives. `frontier --reaching-root` exposes those
alternatives too: 37 → 39 open items (1 → 2 bare; 36 → 37 sourced), including
the two pilot cells and the still-open stage-4 conclusion. This increase is
an exposed dependency, not a successful discharge.

| Result | From | To | Kind |
| --- | --- | --- | --- |
| `BRIDGE-ARIST-POTENCY-ANALYSIS-NON-SIMULTANEITY` | Aristotle, *Met.* IX.6 analysis of potency | Aquinas' non-simultaneity premise (root path) | cross-source implication; moves the open item to the Aristotle reading (`docs/act-potency-theory.md` point 2) |
| `BRIDGE-ARIST-MOTION-ANALYSIS-MOVED-AS-IN-POTENCY` | Aristotle, *Phys.* III.1 definition of motion | Aquinas' "moved only as in potency" (root path) | cross-source implication; same caveat |
| `BRIDGE-STAGE-FOUR-FROM-RESURRECTION-PILOT` | pilot cells "Jesus claims", "rose" | stage 4 (root path) | transcription: conjunction assembly; both cells and stage 4 remain open |
| `BRIDGE-RESURRECTION-PILOT-GOD-EXISTS` | stage 1 `GodExists` | pilot existence cell | transcription: definitional identity |
| `BRIDGE-SECUNDA-SECOND-CAUSES-RELEVANT-RESPECT` | strong per se premise of the secunda via | its relevant-respect reading | implication between two readings |
| `BRIDGE-PER-SE-REGRESS-FINITE-GROUNDING` | secunda via no-regress, excluded middle, finite-grounding theorem | new `STMT-EVERY-BEING-HAS-FINITE-PER-SE-PATH-TO-UNCAUSED` | shared vocabulary (Aquinas `CausesAsCaused` with `Causality.FiniteCausalPath`) |
| `BRIDGE-TERTIA-PLENITUDE-POSSIBLE-NOT-BE-SOMETIME-IS-NOT` | plenitude, infinite past | "what can not-be, at some time is not" | implication inside the tertia via |
| `BRIDGE-TERTIA-NECESSITY-CAUSE-OR-NOT-FROM-EXCLUDED-MIDDLE` | excluded middle | tertia via case split | instance of excluded middle |
| `BRIDGE-QUINTA-REGULAR-BODIES-ALL-TO-SOME` | quinta via first premise, universal reading | its existential reading | implication between two readings |
| `BRIDGE-IV7-EXCLUDED-MIDDLE-AFFIRMING-OR-DENYING-TRUE-OR-FALSE` | excluded middle, truth by composition | *Met.* IV.7 reading B, second half | derivation |
| `BRIDGE-IV7-READING-B-HALVES-YIELD-BIVALENCE` | reading B's two halves | bivalence of thought | derivation |
| `BRIDGE-IV7-EVERY-PROPOSITION-TO-EVERY-OBJECT-OF-THOUGHT` | the unattributed extension | the sourced first half | implication between two readings |
| `BRIDGE-IV7-CONTRADICTORY-PAIR-FROM-EXCLUDED-MIDDLE` | excluded middle | change argument's conclusion | instance of excluded middle |
| `BRIDGE-SCG-INNOVATING-CAUSE-TIMAEUS-DISTINCT-CAUSE` | SCG I.13 innovating cause | *Timaeus* 28a distinct-cause schema | transcription: schema instance (`DISAMB-COMING-TO-BE`) |

One relation was added for a countermodel that is not an inference:
`REL-TELEONOMY-DICHOTOMY-ATTACKS-REGULAR-BEST-BY-CHANCE-OR-INTENTION`.

## Candidates for the next batch

Each entry says what blocks it. None of these was done in batch 1.

<!-- BEGIN GENERATED: docs/bridges/candidates list -->
- **Plato's Forms (27-statement component) to the quarta via and *Met.* II.1,
  993b24-26.** `ExplanatoryParticipation` and `UniformSelfPredication` look
  like the cause-of-quality premise, but the Forms vocabulary has no `MoreIn`
  and no causal relation; `DISAMB-PLATONIC-CAUSE` forbids identifying the
  exemplar with a maker or cause. A bridge needs an explicit, sourced bridge
  premise mapping `Explains` to `CausesIn` (e.g. Aquinas on participation,
  ST I q.44 a.1). The Fourth Way files are under repair (#386).
- **Hiddenness `GodExists` to stage 1.** `TruthCore.Hiddenness.Sig` indexes God
  by world; its header asks for a separate identification bridge. Needs a
  premise relating `Sig.God actual` to `Signature.IsGod`.
- **Physics VII.1 (`STMT-MOVED-MOVER-SERIES-CANNOT-LACK-FIRST`,
  `STMT-EVERY-MOVING-THING-MOVED-BY-SOMETHING`) to the prima via
  (`STMT-NO-INFINITE-PER-SE-MOVER-SERIES`,
  `STMT-WHATEVER-IS-MOVED-IS-MOVED-BY-ANOTHER`).** The Physics readings are opaque
  atoms; wait for the typed re-formalization (#401 item 1).
- **Prima via metatheorems.** `STMT-ABSOLUTE-UNMOVED-MOVER-ENTAILS-RELATIVE` and
  `STMT-STRONG-PRIMA-VIA-PREMISES-ENTAIL-WEAK-PREMISES` are singletons. Composing
  them (e.g. `STMT-FIRST-UNMOVED-MOVER-CANNOT-BE-LACKING` with the first to give
  `STMT-RELATIVELY-UNMOVED-MOVER-CANNOT-BE-LACKING`) connects them, but both
  endpoints are already in the giant component and the proof is two steps.
- **Resurrection pilot reading bridges.** `STMT-PILOT-BRIDGE-*` with the reports
  `STMT-PILOT-REPORT-*` give E0-E5 (`STMT-PILOT-E0` to `-E5`) by modus ponens.
  Each would be a transcription (the bridge's consequent is the conclusion) and
  the E-findings do not reach stage 4, so they would form six new small
  components rather than join the giant one.
- **Grim Reaper to a finite past.** `STMT-GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE`
  bears on `STMT-PAST-IS-FINITE` only through a sourced premise that an
  infinite past permits such a schedule (Koons, Pruss).
- **Gödel/Scott singletons.** `STMT-SCOTT-EMPTY-PROPERTY-NOT-ESSENCE` against
  `STMT-GOEDEL-1970-EMPTY-PROPERTY-IS-ESSENCE` (two essence definitions) and
  `STMT-GOEDEL-1970-POSITIVE-CLOSED-UNDER-CONJUNCTION`: a bridge lemma between
  the two `Essence` definitions would connect the two AFP vocabularies.
- **Modal research fixtures.** `TruthCore.Modal.S5Research` and
  `TruthCore.Isabelle.AFP.GoedelGod` each define frames; a frame-translation
  lemma would connect `STMT-MODAL-S5-CONCEIVED-COLLAPSE` with
  `STMT-SCOTT-MODAL-COLLAPSE` (invariant 17).
- **Excluded-middle family.** `STMT-EXCLUDED-MIDDLE-NOT-DENIABLE`,
  `STMT-EXCLUDED-MIDDLE-IFF-DOUBLE-NEGATION-ELIMINATION` and the intuitionism
  component are premise-free theorems or rival-theory records; a bridge from
  `STMT-EXCLUDED-MIDDLE` would re-prove what is already proved. Relations only.
- **Q11 countermodels** (`STMT-Q11-UNIQUENESS-FAILS-WITHOUT-*`) and **Kant
  countermodels** show premise independence; there is no relation predicate for
  independence, and they imply nothing in the giant component.
- **Russell on existence** (`STMT-RUSSELL-EXISTENCE-*`) against stage 1: needs a
  bridge from the quantifier reading of existence to the case's `∃ g, IsGod g`.
<!-- END GENERATED -->

## Repair of closure metadata (2026-10-26)

The original description of conjunction assembly and lambda instantiation as
new frontier-closing proofs was rejected: theorem consequence is distinct
from philosophical defense. The four schema/identity instances now declare
`transcription: instantiation`; the pilot conjunction declares
`transcription: assembly`. No Lean theorem or frozen Challenge changed. The
candidate entries above preserve the remaining vocabulary and source gaps.
