# Maximum in an order

Issue #412, schema 2, isolates one consequence of the Fourth Way's degree
reasoning: **if every distinct cause of a degree is strictly higher in that
same order, a maximal member has no distinct cause of that degree**. This is
not the converse assertion that a maximum causes everything below it.

`TruthCore.Logic.MaximumOrder.System` holds a chosen cause-of-degree relation
on a Mathlib `Preorder`. Its `CausesRaiseDegree` condition is separate data:
`∀ c x, c ≠ x → causes c x → x < c`. Mathlib `IsMax m` excludes `m < c`;
applying the two conditions derives the contradiction. The theorem excludes
only distinct causes, only in the selected relation and respect. It does not
exclude self-causation or a cause in another respect. A preorder can have tied
members and incomparable maximal members; `IsMax` is not `IsGreatest`.

The certificate package is `MAXIMUM-ORDER-SCHEMA` in
`TruthCore.Results.Logic.MaximumOrderSchema`. Its Comparator configuration
also checks the two instance theorems and four omission/control theorems.
The public corpus result records keep the three advertised conclusions
separate, with one independent statement for each.

## Proved conditional instances

`STMT-FOURTH-WAY-MAXIMUM-SCHEMA-INSTANCES` explicitly quantifies the three
named respects `esse`, `bonum`, and `verum`. For each chosen respect, it takes
`HomogeneousScaleReading` and the unrestricted
`CauseOfQualityInAnotherIsMoreSuchReading` as conditional inputs. The exact
existing theorem `HomogeneousScaleReading.isMaximumIn_iff_isMax` from #386
translates the corpus maximum into Mathlib maximality.
`HomogeneousScaleReading.causesRaiseDegree` translates the causal comparative;
`System.maximal_has_no_distinct_cause` then supplies the conclusion. The proof
also works for other respects; the named family makes the requested being,
goodness and truth uses explicit. Their respects, scales and maxima are not
identified with each other.

`STMT-ATTRIBUTION-MAXIMUM-SCHEMA-INSTANCE` first uses the exact #386 theorem
`ApproachToPrimaryReading.homogeneousLift`. The induced preorder on beings is
`Preorder.lift near`; the degrees of approach have their own preorder. This
step needs the additional `∀ x, InAct x r`, since the approach reading itself
only supplies possession by the primary. It then applies the same two
representation lemmas and generic theorem. Strict primacy, the creature bridge,
and the primary-causes-creatures clause are unused. Consequently this instance
does not establish the unrestricted causal comparative on the attribution
reading: `QUARTA-VIA-ATTRIBUTION-RESTRICTS-CAUSE-MORE-SUCH` still exhibits its
failure for secondary causes.

These are conditional mathematical transfers, not newly attributed source
claims. The consulted materialized witnesses were `AQUINAS-ST-I-Q2-A3`,
`ARIST-MET-II-1`, `AQUINAS-ST-I-Q3-A5` and `AQUINAS-ST-I-Q13-A5`. Their existing
readings and limitations are preserved. In particular, Aristotle's Metaphysics
II.1 993b24–31 concerns the synonymous quality; the existing unrestricted
cause-more-such predicate contains an open strengthening beyond that condition.
No new assertion extends that source attribution.

## Discriminating controls and skeptical reply

All four controls are proved in the certificate package:

- Ordered `Bool` with no causal edges has greatest member `true`, lower member
  `false`, and satisfies causal ascent vacuously. Yet `true` does not cause
  `false`. Thus maximum plus ascent does not yield maximum-causes-all.
- Ordered `Bool` with a causal edge from `false` to `true` makes the maximum
  have a distinct cause. It violates ascent, showing why that condition is
  needed for the schema's conclusion.
- `Nat` has no maximal member: `m + 1` exceeds each proposed maximum. Even
  nonemptiness and a total scale with strict comparisons do not yield existence.
- Two distinct Boolean beings assigned the same `Unit` degree are both
  maximal in the pulled-back preorder. Representation by degrees does not
  yield uniqueness.

The strongest skeptical response is that these representations and the causal
ascent condition are precisely what needs defending philosophically. A
homogeneous order on being may be inappropriate; a cause may contain a
perfection virtually rather than formally; an attribution order may have
secondary causes that do not ascend; a maximum may fail to exist. The skeptic
can accept every proved schema and transfer while withholding those conditions.
Nothing in the proof forces their acceptance. In particular, absence of a
distinct cause of a maximum supplies neither its existence nor its universal
causal power nor its identity with God. Further source arguments and
independently defended bridges are required.

## Premise comparison

Intended and actual root-path change: **none**. These universally quantified
conditional theorems introduce no new root arguments or designated routes.
The existing maximum-causes-all, cause-more-such, maximum-existence and naming
premises remain open exactly where they were open before.

For the homogeneous instance, retained conditions are the existing homogeneous
representation and unrestricted causal comparative. The maximum assumption
remains local to the conditional. For attribution, universal possession is an
additional explicit local condition beyond the approach reading; the causal
comparative is also conditional. No condition is sourced or discharged by
registration. Strict primacy, creatures and the causal clause about the primary
are omitted from this transfer because it proves a different, weaker conclusion
than #386's genus-principle derivation. This omission does not refute those
premises or replace that derivation.

Verification at the completed local proof package: all seven Comparator
obligations and solution NanoDa passed; full library NanoDa checked 21,384
declarations with no typechecker errors. Registration was then checked against
the merged #447 contract by live bind-check (424 bound, two historical pins,
zero mismatches, including the finite-model gate). These counts describe that
repository head, not the truth of the conditional philosophical inputs.
