# Universal fusion, causal externality and grounding

Investigation: #328 / #325, with the open composition-to-dependence interface in
#319. This is one bounded comparison, not completion of a worldview or issue.

The question is whether allowing every nonempty plurality to fuse already
requires an additional uniting cause, rules it out, or determines explanatory
priority. The strongest universalist reply allows arbitrary fusions while
reserving organization, ordinary kind and causal integration for further
structure. A rival can demand an actual uniting cause for composite substances.
Those positions do not yet contradict one another: fusion, substance and causal
sufficiency are different claims.

## Source evidence and interpretation

`VARZI-MEREOLOGY-COMPOSITION` pins Achille C. Varzi's *Mereology*, SEP Fall2025
archive, §4.1–4.5. The materialized entire range was read. Relevant locators:

- §4.2, definitions39_1–39_3: a least upper bound alone may admit irrelevant
  extra parts; Sum2 additionally requires every part to overlap a selected member.
- §4.3, definition52_2: generalized Sum2 combines the upper-bound and no-extra-part
  clauses. §4.4(P.15_i) explains unrestricted composition with nonemptiness.
- §4.4, definition59 and the following discussion: the universal entity covers
  the domain. The discussion of Ascent/P.19 explains the incompatibility with a
  domain in which every entity is properly included in a greater one.
- §4.5: an affirmative universalist answer appeals to the difficulty of a
  principled restriction, permits ignored scattered sums, and separates ordinary
  judgments of unity from existence. The discussion explicitly notes a separate
  cross-category problem when the domain includes different ontological kinds.
- §4.5 distinguishes composition-as-identity responses to ontological exuberance
  and notes that these admit different formulations; unrestricted fusion and
  many-one identity are not silently equated here.

This is an author's encyclopedia exposition, **not** a witness to the unread2008
article or to every cited philosopher's primary argument. Columbia selected and
bibliography pages gave HTTP403 to source-evidence fetches; search previews were
not promoted to evidence. The fixed SEP archive yielded matching byte and text
hashes on two fetches, then materialized successfully. An initial incipit was
corrected to preserve the extraction's newline. WaybackCDX returned403 and a save
request timed out after10s; no fallback is claimed. No source-derived corpus
claim attributes the following mathematical certificate to Varzi.

## Exact formal profile and certificate

`TruthCore.Mereology.UniversalFusionBoundary.Fusion` uses a Mathlib partial order,
common-part overlap, and the Sum2 upper-bound/no-extra-parts clauses.
`Unrestricted` quantifies over every nonempty Lean `Set` of that carrier. That is
an explicit second-order analyst profile; its equivalence to any particular
first-order schema is not asserted. The mathematical carrier interpretation is
fixed at one stage. No modal, temporal or causal relation is imported by notation.

The theorem `TruthCore.Results.Mereology.UniversalFusionBoundary.checks` proves
`Boundary`, comprising:

1. On any inhabited supplied partial order, unrestricted fusion gives a greatest
   entity, by applying the upper-bound clause to the whole domain.
2. If `Covers material u` and an admitted candidate is not a part of `u`, that
   candidate cannot satisfy `material`. The predicate is explicit; it need not
   cover every entity in a larger metaphysical domain.
3. `Body`, the nonempty subsets of two constituents, has unrestricted Sum2 fusion.
   A nonempty family fuses by union; an inhabited part of the union overlaps a
   member through a singleton. This proves actual no-extra-parts fusion, rather
   than merely selecting an arbitrary upper bound.
4. The greatest whole is composite. Interpreting the candidate ground relation
   as strict parthood gives it, and every composite in the same carrier, a
   numerically distinct candidate ground. That relation is irreflexive.
5. Interpreting the candidate ground relation as empty leaves **the same**
   carrier, parthood and every fusion fact intact, but fails the distinct-ground
   requirement at the composite whole. The interpretation of grounding remains
   additional data; its metaphysical adequacy is unproved in either variant.
6. For **every** candidate cause relation on `Body`, there is no cause outside
   the parts of its greatest whole. This does not exclude distinct proper-part
   causes: item4 witnesses the difference.
7. A separately enlarged carrier has an additional candidate stipulated as
   nonmaterial and not part of the material whole. This last control asserts
   nonparthood, not actual causal activity or metaphysical possibility.

Mathlib supplies the subset partial order and set mathematics. There is no
hand-rolled replacement for a Mathlib mathematical notion. No non-Mathlib Lean
dependency is used. The allowed axioms are exactly the repository Mathlib policy:
`propext`, `Classical.choice`, `Quot.sound`.

The q3 uniting-cause premise requires numerical distinction, not nonparthood.
The necessary-being survey separately considers a stronger outside-thing-and-parts
notion. `DISAMB-FUSION-CAUSE-EXTERNALITY` links these existing senses and the new
model senses. We refute neither source premise by replacing one with the other.
In particular, a universal **material** fusion does not prohibit a nonmaterial
cause, and no cause relation here is automatically `CausesIn` at esse.

## Common question set: affirmative replies and remaining commitments

| Shared question | Universalist reply in this slice | Remaining commitment / strongest reply |
| --- | --- | --- |
| Q-COMPOSITION | Every admitted nonempty plurality has a Sum2 fusion; arbitrary scattered sums are allowed. | Why unrestricted rather than restricted composition is true of reality remains open; the model supplies consistency in this profile only. |
| Q-UNITY | Fusion existence is settled separately from causal integration and substantial unity. | No criterion for substances or organized ordinary kinds is proved; a hylomorphist may defend such a criterion without denying arbitrary fusions. |
| Q-LIFE-SOUL | Permitting an organism's fusion does not supply a theory of life, mind or soul. | Unexplained by this model; the existing Vitalism stress test, not this theorem, compares its richer behavioral signature. |
| Q-IDENTITY | Entities in `Body` have extensional set identity at one stage. | Persistence through replacement and strong many-one composition-as-identity remain separate; the static model does not adjudicate them. |
| Q-GROUNDING | Strict-part priority and the empty relation both preserve all fusion facts. | Whether parts, wholes, another being, or a global structure explains existence needs a defended additional relation and adequacy standard. |
| Q-EXPLANATION | Fusion existence need not add a new agent or manufacture event within the formal profile. | No sufficient ontological explanation follows; even the strict-part relation is only an interpretation, not a defended explanation. |
| Q-ULTIMATE | Unrestricted fusion supplies a greatest entity **of the stipulated domain**. | Greatest material whole is not thereby an ultimate cause, necessary existent, simple being, God, or a sufficient reason. |

The strict-part model is a positive structural alternative to simply denying a
uniting-cause conclusion; the empty-relation model states its explanatory gap
rather than calling it solved. Neither establishes an adequate complete
universalist worldview. Priority monism, restricted composition and nihilist
arrangement accounts retain their distinct questions and replacement obligations.

## Reuse, verification and premise comparison

Inventory found `Vitalism`'s turnover/organization vocabulary,
`RegressDomains.parthood`'s partial-order adapter, and
`PowerExistenceBoundary.Composite`'s finite proper-component model. None supplies
fusion axioms. This module reuses Mathlib's order/set vocabulary instead of
misidentifying those existing meanings. It adds no shared definition edits.

The Challenge was frozen before Solution, SHA256
`9184056c1ef2edc705e3969f3ea5e29999d160b09526d7bf9c52956fcc12f067`.
Shared diagnostics at preview `de591c1d405b7279d470d06d4ebb1160e61f78ad` accepted
combined exact source/Solution content SHA256
`33f6fc1a4eba6d3ddd09210cbb8f68745cd34b0d29a3360e4bc51482d39fee56`,
with no errors and only the expected axiom report. The earlier broad Set.Lattice
import produced a deprecation warning; it was narrowed to Lattice.Bounded without
changing the certificate. Final build, binding, Comparator and NanoDa remain CI
obligations, not consequences of an empty diagnostic list.

Intended and actual root-premise change: **none**. All existing root premises,
including the actual composite-uniting-cause premise, remain open as before.
The result clarifies the strength and domain of a potential causal interface;
it does not discharge it. No inference to `STMT-CATHOLICISM-TRUE` is added.

Next decisive questions: which actual composites are substances; whether those
compositions require an actual distinct cause; whether any further nonparthood
restriction is defended; and whether priority comes from parthood, a material
process, a distinct agent, or another adequate account. These remain philosophical
obligations rather than consequences of a formal union operation.
