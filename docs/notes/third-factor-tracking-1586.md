# Quantifying Enoch's third-factor reply (#1586)

Analyst formulation, attribution deferred. The existing claim
`ENOCH-THIRD-FACTOR-ACCESS-REPLY` (Enoch 2010, §§5.1–5.3, pp. 427–434, read from
the pinned witness in #651) and `STMT-STREET-DARWINIAN-ACCESS-CHALLENGE` are the
sourced commitments. Neither author states a rate, a distribution or an error
bound; every number below is an analyst input or a stipulated model value. The
source reading is in `docs/naturalistic-moral-realism.md`, "Moral access
comparison".

Lean: `TruthCore.Logic.ThirdFactorTracking` (vocabulary) and
`TruthCore.Results.Logic.ThirdFactorTracking` (five results); spec
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
  other than survival. The binary gap counts both directions. Even the one-way
  part `μ{F ∧ ¬M}` is only made plausible, not small, since survival is not
  always good.
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
2. **One-sided bound** (`oneSidedThirdFactorBound`, premises
   `EndorsedAgainstFactorAtMost`, `FactorWithoutReasonAtMost`, both OPEN). For
   binary verdicts, `{B ∧ ¬M} ⊆ {B ∧ ¬F} ∪ {F ∧ ¬M}`, so
   `μ{B ∧ ¬M} ≤ d₁ + d₂`, again with no independence. Its second premise is
   the only direction Enoch's premise bears on, so this is the strongest
   quantified form of his modest correlation: what selection disposes us to
   endorse mostly has a reason behind it. It says nothing about reasons `B`
   fails to endorse.
3. **Sharpness** (`binaryErrorAccounting`). For binary verdicts,
   `{B ≠ M} = {B ≠ F} Δ {F ≠ M}`, so
   `μ{B ≠ M} + 2μ(both) = μ{B ≠ F} + μ{F ≠ M}`. For a finite measure, the
   bound taken at the actual error rates is attained exactly when the two error
   sets almost surely never overlap (null overlap), and coinciding binary errors
   cancel. For non-binary verdicts two errors need not cancel. The theorem is
   silent there.
4. **Subclass transfer** (`subclassGapBound`). For a measurable class `S`,
   `μ[{F ≠ M} | S] ≤ μ{F ≠ M} / μ S`. An aggregate gap bounds the gap in a light
   class only after dividing by its weight. The theorem holds for any pair of
   assignments, so it also applies to `(B, F)`: an aggregate selection error
   `e₁` bounds the hard-case selection error only by `e₁ / μ S`.
5. **Models** (`thirdFactorModels`, four equally weighted cases). (a) Errors of
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
  injury, with `M` pro tanto). Here Enoch's normative premise makes the one-way
  `F`-to-`M` direction plausible, not small. With open bounds `d₁` and `d₂`,
  result 2 gives a quantified one-sided correlation: wrongly endorsed acts are
  at most `d₁ + d₂`. This is the modest correlation Enoch says he aims to
  explain (§5.1), and the reply is coherent in exactly that scope. The
  two-sided correlation `1 − e₁ − e₂` needs, in addition, a further OPEN bound
  on `μ{¬F ∧ M}` over the adaptive range: acts with a pro tanto reason that the
  factor does not favour. Enoch's premise does not supply that bound.
- **Impartial/hard-case target** (`M` all-things-considered or impartial,
  restricted to conflict cases). Here `F` diverges from the realist's own
  impartial verdicts by the definition of the class, so the gap is exactly 1
  there and the union bound is vacuous. Result 4 shows that a small aggregate
  `e₂` cannot be split down to this class except by dividing by its weight.
  Model (c) shows that the aggregate guarantee can hold, and even be attained,
  while a judgment equal to `F` fails on every hard case.

  The claim that **actual** selected judgments fail there needs a further
  **OPEN input**: hard cases lie in the selected range, with a small
  *conditional* selection error `μ[B ≠ F | S]`. An aggregate `e₁` does not give
  this, since result 4 applied to `(B, F)` dilutes it to `e₁ / μ S`. Where
  `F ≠ M` almost surely on `S`, binary accounting under the conditional measure
  gives `μ[B = M | S] = μ[B ≠ F | S]`. So the selected judgment's hard-case
  accuracy is exactly how far it departs from `F` there. Hard-case accuracy
  comes either from `B` departing from `F` on `S` or from a separate route `R`.

**Enoch's strongest reply.** He does not claim that selection alone yields
accurate impartial verdicts. He claims (i) a modest correlation, (ii) that
reasoning from reasonably good starting points can extend and correct it, and
(iii) residual epistemic luck (§§5.1, 5.3; note 44 separates explaining the
correlation, and possibly defeating a defeater, from directly justifying
beliefs). Nothing here refutes that reply. The results locate what it needs. On
hard cases the accuracy of reflective verdicts `R` has to come from the
reliability of the reasoning, a quantity such as `μ[{R ≠ M} | hard]`. The
reasoning is a further reliability premise whose inputs the third factor
shapes, since it proceeds from third-factor-supported starting points. Its
reliability on conflict cases is not bounded by `e₁` or `e₂`, and a chain bound
through `B` and `F` is vacuous there. That reliability is the open question,
as it is for the reasoning and inquiry routes in the Railton, Boyd and q.94
rows.

## Scope limitation

The strongest limit is substantive, not hypothetical. The certified bound
transfers only on the distribution and verdict type for which `e₂` is
calibrated. The qualified pro tanto goodness of survival bears at most on one
direction of the pro tanto gap, `μ{F ∧ ¬M}`, and even that only qualifiedly.
The reverse direction `μ{¬F ∧ M}` is unbounded by it. On impartial conflict
cases, the realist's own first-order verdicts make `F` and `M` diverge.

So the third factor yields the one-sided adaptive/self-regarding correlation
(result 2) under the open `d₁` and `d₂`. The two-sided correlation needs a
further open bound on `μ{¬F ∧ M}`. Hard-case accuracy rests on a further
reasoning-reliability premise whose inputs the third factor shapes, and on the
open conditional selection premise above.

## Open

- Empirical calibration of `e₁` (how closely selected judgments follow `F` on a
  specified range) and the normative/empirical calibration of `e₂` for each
  verdict type. No values are supplied or assumed.
- A bound on `μ{¬F ∧ M}` (reasons the factor does not favour) for each target
  range, and values of `d₁` and `d₂`.
- Whether hard cases lie in the selected range with small conditional selection
  error `μ[B ≠ F | S]`.
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
