# Quantifying Enoch's third-factor reply (#1586)

Analyst formulation, attribution deferred. The existing claim
`ENOCH-THIRD-FACTOR-ACCESS-REPLY` (Enoch 2010, §§5.1–5.3, pp. 427–434, read from
the pinned witness in #651) and `STMT-STREET-DARWINIAN-ACCESS-CHALLENGE` are the
sourced commitments. Neither author states a rate, a distribution or an error
bound; every number below is an analyst input or a stipulated model value. The
source reading is in `docs/naturalistic-moral-realism.md`, "Moral access
comparison".

Lean: `TruthCore.Logic.ThirdFactorTracking` (vocabulary) and
`TruthCore.Results.Logic.ThirdFactorTracking` (four results); spec
`specs/third-factor-tracking-1586.toml`.

## What `B`, `F` and `M` mean

One distribution `μ` of cases is fixed: a population of situations calling for
an evaluative verdict on an act or attitude. On each case:

- `B` is the selected-for judgment, for example "this act is to be done";
- `F` is the third factor: whether the act promotes the survival or reproductive
  goods selection responded to. It is specified without reference to `B` or `M`;
- `M` is the normative truth about the same act, under **one fixed verdict
  type**: pro tanto reason, all-things-considered rightness or impartial
  obligation.

The comparison of `F` with `M` matters for truth because `M` is what `B`
purports to report. `F` is relevant to `M` only through a first-order normative
premise. Enoch's is that survival is good, in a qualified sense: not always good,
not overriding, not ultimate or intrinsic (§5.3). The gap `e₂ = μ{F ≠ M}`
therefore depends on the verdict type:

- **Pro tanto verdicts.** Enoch's premise at most supports the one-way inclusion
  "where `F` holds, there is a pro tanto reason". It does not bound the cases
  where `F` fails and a pro tanto reason holds anyway, since there are reasons
  other than survival. The binary gap counts both directions.
- **All-things-considered verdicts.** A pro tanto reason can be outweighed, so
  the premise does not bound `e₂` at all.
- **Impartial verdicts.** These give weight to non-kin and strangers whatever
  they contribute to the agent's fitness. In a *conflict case*, where the
  fitness-favoured option is the one the realist's own impartial verdict rejects
  (costly help to a stranger, restraint toward an outgroup rival when harming
  would pay), `F` and `M` differ because of how the case class is defined. They
  do not differ because of an independent empirical surprise.

## Certified results

1. **Union bound without independence** (`thirdFactorUnionBound`, premises
   `SelectionErrorAtMost`, `FactorTruthGapAtMost`, both OPEN). From
   `{B ≠ M} ⊆ {B ≠ F} ∪ {F ≠ M}` and subadditivity, `μ{B ≠ M} ≤ e₁ + e₂`.
   For a probability measure, `μ{B = M} ≥ 1 − (e₁ + e₂)` (truncated). This holds
   for verdicts of any type, with no independence or common-cause structure
   between the two errors. Mathlib's `measure_symmDiff_le` is the same
   triangle inequality stated for sets. `ThresholdBelief.SupportBoundary` (#1063)
   is the finite intersection form; this one is general.
2. **Sharpness** (`binaryErrorAccounting`). For binary verdicts,
   `{B ≠ M} = {B ≠ F} Δ {F ≠ M}`, so
   `μ{B ≠ M} + 2μ(both) = μ{B ≠ F} + μ{F ≠ M}`. The bound is attained by the
   actual rates exactly when the two error sets are almost surely disjoint, and
   coinciding binary errors cancel. For non-binary verdicts two errors need not
   cancel. The theorem is silent there.
3. **Subclass transfer** (`subclassGapBound`). For a measurable class `S`,
   `μ[{F ≠ M} | S] ≤ μ{F ≠ M} / μ S`. An aggregate gap bounds the gap in a light
   class only after dividing by its weight.
4. **Models** (`thirdFactorModels`, four equally weighted cases). (a) Errors of
   1/4 and 1/4 on different cases give agreement exactly 1/2, so the bound is
   sharp. (b) The same rates on the same case give agreement 1. (c) `B = F` and
   a gap of 1/4 on the one impartial hard case give aggregate agreement 3/4,
   which attains the bound. Agreement is 0 on the hard case and 1 on the adaptive
   cases, and the conditioned gap 1 attains the subclass bound.

## Adaptive and impartial targets compared

Fix `B` close to `F`. This is the selection premise. On the analyst's reading it
is what Street's adaptive-link explanation supplies for the selected range;
`e₁` is still an empirical input.

- **Adaptive/self-regarding target** (care for one's own offspring, avoiding
  injury, with `M` pro tanto). Here Enoch's normative premise makes the
  `F`-to-`M` direction plausible. The third factor then gives a real, quantified
  correlation `1 − e₁ − e₂` on that distribution. This is the modest
  correlation Enoch says he aims to explain (§5.1), and the reply is coherent in
  exactly that scope.
- **Impartial/hard-case target** (`M` all-things-considered or impartial,
  restricted to conflict cases). The selection premise keeps `B` near `F`, and
  `F` diverges from the realist's own impartial verdicts by the definition of
  the class. The union bound is then vacuous there (`e₂` near 1). Result 3
  shows that a small aggregate `e₂` cannot be split down to this class except
  by dividing by its weight. Model (c) shows that the aggregate guarantee can
  hold, and even be attained, while the selected judgment fails on every hard
  case.

**Enoch's strongest reply.** He does not claim that selection alone yields
accurate impartial verdicts. He claims (i) a modest correlation, (ii) that
reasoning from reasonably good starting points can extend and correct it, and
(iii) residual epistemic luck (§§5.1, 5.3; note 44 separates explaining the
correlation, and possibly defeating a defeater, from directly justifying
beliefs). Nothing here refutes that reply. The results locate what it needs. On
hard cases the accuracy of reflective verdicts `R` has to come from the
reliability of the reasoning, a quantity such as `μ[{R ≠ M} | hard]`. Neither
`e₁` nor `e₂` bounds it, and a chain bound through `B` and `F` would make it
worse, not better. The reasoning step is then an independent access mechanism,
like the reasoning and inquiry routes in the Railton, Boyd and q.94 rows. Its
reliability on impartial conflict cases is the open question. The third factor
does not answer it.

## Scope limitation

The strongest limit is substantive, not hypothetical. The certified bound
transfers only on the distribution and verdict type for which `e₂` is
calibrated. The qualified pro tanto goodness of survival bounds at most one
direction of the pro tanto gap. On impartial conflict cases, the realist's own
first-order verdicts make `F` and `M` diverge. So the third factor explains the
adaptive/self-regarding part of the correlation. Hard-case accuracy rests on a
separate reasoning-reliability premise.

## Open

- Empirical calibration of `e₁` (how closely selected judgments follow `F` on a
  specified range) and the normative/empirical calibration of `e₂` for each
  verdict type. No values are supplied or assumed.
- The weight of conflict cases in any realistic distribution, and whether
  reflective reasoning `R` is reliable on them.
- Non-binary verdicts (graded strength of reasons), where cancellation fails.

## Connections

- Reuses the history-fixed correctness and Street's horns from
  `TruthCore.Logic.DarwinianEpistemicDebunking` (#1585) as context. The
  realist's fixed-truth picture is what makes `M` a fixed target across cases
  here. The cross-history horn is non-probabilistic. This note supplies the
  probabilistic shape of the third-factor answer to its "no relation" premise,
  without deriving Street's "in all likelihood" step.
- Probability vocabulary: Mathlib `uniformOn` and conditional probability, as
  in #1063 (`ThresholdBelief.uniform`) and #1584 (`PrefaceConnectivity`). No
  product or independence structure is needed, so the #1584 product profile is
  not reused.
- #1500 (companions in guilt) is **not** linked. Its premises concern the kind
  and authority of reasons, epistemic and moral (categorical, irreducible,
  functional). None of them is a bound on the error rate of a judgment against
  a factor, so no norm-type premise coincides.
- Informs #1506 (epistemic access/reliability comparisons). It establishes no
  moral realism, access or God claim. These statements are not on a root route,
  so no root premise changes.
