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

## SEP intake: supplementation and the choice of fusion (2026-11-06)

Read-only research delta at public main `13f1d8f2b3f96687248f7aa1a10e288a29a2a2eb`;
implementation and historical attribution deferred. Navigation: current
[SEP Mereology](https://plato.stanford.edu/entries/mereology/), §§3.1–3.4,
§§4.2–4.4, especially P.4/P.5, (31), (39_i), (52_i), and the
P.15 pairing discussion. Current entry substantive revision: 2026-06-27.
This is not a new pinned witness or attributed corpus claim. The existing
Fall2025 witness and its numbering above are unchanged.

The bounded reading distinguishes supplementation from strong supplementation,
and least-upper-bound sums from upper-bound/no-extra-parts sums and sums defined
by identical overlap profiles. Its pairing discussion warns that supplementation
with unrestricted overlap-profile sums does not entail extensional mereology.
It instead identifies supplementation with unrestricted Sum2, strong
supplementation with unrestricted Sum3, and complementation with unrestricted
Sum1 as classical packages. Its atomism discussion also distinguishes atomic
parts from termination of every decomposition chain. No new atom/gunk task is
selected here.

**Actual gap and reuse.** Inventory of all Lean files found no supplementation,
Sum1 or Sum3 axiomatization. Reuse the exact
`TruthCore.Mereology.UniversalFusionBoundary.Overlap`, `.Fusion` (Sum2),
`.Unrestricted`, and Mathlib `PartialOrder`; do not redefine them.
`TruthCore.Results.Mereology.UniversalFusionBoundary.checks` already supplies the
Sum2 greatest-whole and causal/grounding boundaries. Reuse the existing
`TruthCore.Mereology.NecessaryPartFusionDecomposition.OverlapExtensionalParthood`
as the target structural interface: it is currently an explicit open premise,
not a consequence of PartialOrder. Its existing `fusionBelow` and `decompose`
theorems consume that interface. Related/dossiers for
STMT-UNIVERSAL-FUSION-GROUNDING-BOUNDARY and
STMT-OVERLAP-EXTENSIONAL-PARTHOOD, their linked successful attempts, and issues
#325/#328/#346 were inspected. This belongs under #328, with reference mapping
relevant to #346; no new issue is needed.

**Rank 1: the supplementation/fusion bridge and its sharp rival.** On one fixed
partial order define WS as `x < y → ∃ z, z ≤ y ∧ ¬ Overlap z x`, SS as
`¬ x ≤ y → ∃ z, z ≤ x ∧ ¬ Overlap z y`, Sum1 using Mathlib `IsLUB`, and
Sum3 by `∀ p, Overlap p u ↔ ∃ x ∈ family, Overlap p x`.
All unrestricted formation quantifies over nonempty Lean Sets, preserving the
existing explicit second-order profile. Conjectured theorem package, with a
complete informal derivation but no Lean certificate yet:

- WS plus **binary** Sum2 formation already entails SS. Hence existing
  Unrestricted plus WS entails the already-defined OverlapExtensionalParthood.
- Proof: assume every part of x overlaps y and take a Sum2 fusion u of {x,y}.
  Every part p of u overlaps x or y. In the first case a common part q≤p,x
  overlaps y, so p overlaps y as well. Since y≤u, WS rules out y<u; thus u=y
  and x≤y. Contraposition yields SS. This is genuine deduction from typed
  structure; no necessity, cause, modal or ontological existence premise enters.
- SS is equivalent to existing OverlapExtensionalParthood by classical
  contraposition and transitivity. Under SS, the three sum predicates coincide for nonempty families;
  arbitrary-family Sum2 uniqueness follows. Keep composite proper-part
  extensionality separate from equality of overlap profiles and from atom
  identity: distinct atoms share the empty proper-part profile.
- Countermodel candidate: four distinct objects a,b,u,v; the only strict
  comparisons are a<u, b<u, a<v, b<v. It has WS and Sum3 formation for **all 15**
  nonempty families, but fails SS and composite proper-part extensionality.
  Both u and v are Sum2 fusions of {a,b}; {u,v} has no upper bound and hence no
  Sum1 or Sum2 fusion. Thus a selected Sum2 fusion can be nonunique under WS;
  all-family Sum2 existence is the extra commitment that excludes this rival.
  A direct exhaustive Python evaluation of the full order/overlap definitions
  returned WS=true, SS=false, all-nonempty-Sum3=true, all-Sum2=false,
  Sum2({a,b})={u,v}, equal-proper-part-profiles(u,v)=true. This is screening,
  **not** Lean/Comparator/model certification. No atomless finite witness is
  proposed. No causal/grounding interpretation is added.

**Rank 2, optional same-cluster control:** Sum1 formation is also insufficient,
even with SS. Candidate carrier {a,b,c,t}, with exactly a,b,c<t, is a partial
order with WS, SS and every nonempty least upper bound. The least upper bound of
{a,b} is t, but c≤t is disjoint from both, so it is not Sum2 or Sum3; there is no
other sum of those kinds. Complementation of t relative to a fails because
nothing comprises exactly b and c. This candidate was reasoned through but not
executed or Lean-verified. It discriminates lattice closure from no-extra-parts
composition; do not advertise it as another atom/gunk ontology result.

**Strongest case and rival.** An extensionalist can motivate genuine separation:
a parthood difference should have a disjoint remainder, and every nonempty
plurality should have an upper-bound/no-extra-parts whole. The first theorem
shows these commitments force overlap individuation. The strongest retained
rival accepts disjoint supplementation and unrestricted overlap-profile
composition while allowing distinct composites with identical constituents.
The four-object order positively realizes that declared mathematical rival;
it does not establish material coincidence or the metaphysical adequacy of such
objects. Weakening to Sum3 also loses containment of each selected member in
the purported sum: the Sum3 witness u for {u,v} does not contain v.

**Implementer brief:**
1. Target: certify WS + binary Sum2 → SS ↔ existing overlap-extensional parthood,
   and one joint four-object WS+unrestricted-Sum3 anti-extensional certificate.
2. Reuse: exact existing Overlap/Fusion/Unrestricted, PartialOrder, and
   NecessaryPartFusionDecomposition.OverlapExtensionalParthood; import prior
   results rather than replacing their premises or recertifying unchanged work.
3. Missing: formalize only the distinct supplementation/Sum3 interfaces and
   shared-order proof, freeze Challenge before Solution, then certify all-family
   rival semantics and explicit failures; optional Sum1 control only if coherent.
4. Premise comparison: retain fixed classical partial-order/common-part
   semantics and nonempty formation; add WS to existing Sum2 formation to derive
   the structural interface conditionally. Rival replaces Sum2 formation with
   strictly weaker Sum3 formation and keeps WS. No actual ontology, necessity,
   causal bridge, source truth, philosophical applicability or root premise is
   discharged. Existing modal fusion-necessity assumptions remain open.

Rejected duplicates: greatest whole from existing unrestricted Sum2;
grounding/cause independence on the existing Body; atomicity-versus-descent
termination; arrangement/Theseus persistence. Remaining broader matrix cases
are deliberately deferred. No new Lean, claim, source, passage, result, issue,
service, extraction infrastructure, build or proof verification was added by
this intake.

### Issue #1050 implementation supersedes the screening-only status above

The selected rank-1 cluster now has vocabulary and frozen Challenge/Solution in
`TruthCore/Mereology/SupplementationFusion.lean` and
`TruthCore/Results/Mereology/SupplementationFusion/`. The rank-2 Sum1 control
remains deferred and has no new declaration or claimed certificate.

The five advertised results are `STRONG-FROM-WEAK-BINARY-FUSION`,
`MEREOLOGICAL-SEPARATION-CHARACTERIZATION`, `SUM2-SUM3-COMPARISON`,
`STRONG-SUM3-GREATEST-ENTITY`, and `SUPPLEMENTATION-FUSION-RIVAL`.
The first requires only WS and binary Sum2 on the supplied partial order;
it does not require atomism, all-family formation or an inhabited carrier.
The second proves SS iff the **existing** overlap-extensional interface,
without asserting either side unconditionally. The third derives pointwise
Sum2/Sum3 equivalence under SS. Its `overlapOfFusion` helper needs no SS in the
Sum2-to-Sum3 direction. The greatest-entity corollary lists SS, nonempty-family
Sum3 formation **and carrier inhabitation**; it converts to genuine Sum2 and
imports the first conjunct of existing `UniversalFusionBoundary.checks`.

The rival theorem proves the joint fourteen-conjunct certificate of the same
four-object order, including all-nonempty-Set Sum3 (not merely the fifteen
screened inputs), duplicate composites, all advertised failures and absence of
a null object. It also checks the specific missing containment: u is a Sum3
witness for {u,v}, yet v is not part of u. Both u and v are Sum2 fusions of
{a,b}. Thus unrestricted overlap-profile composition alone supplies neither
unique individuation nor a greatest domain whole, even with WS. The strongest
rival retains both supplementation and liberal overlap-profile composition;
it rejects the further containment commitment that would force SS here.

The ordinary common-part overlap has no nonzero-part correction. Arbitrary
carriers do not silently assume a null object or silently remove one. A null
object would overlap every object; the explicit rival has none. No spatial,
causal, grounding, actuality or modal relation is inferred from the order.

Frozen Challenge SHA256:
`44f29c06d79b59fb30cb4d15028409d9a2b50c22bea169a4a8af8f9babf7da6d`.
Focused build is clean and the five exact result bindings pass. The first
binding run correctly found carrier inhabitation missing from the metadata;
the premise record now binds the already-frozen `Nonempty B` hypothesis.
No theorem, assumption or Challenge was changed to repair it. All five Comparator/result NanoDa checks now pass; actual axiom probes for
each use exactly `propext`, `Classical.choice`, `Quot.sound`. The existing finite
registry requires zero-axiom model/enumeration/evaluation terms, so this
Mathlib certificate is not registered there and no tooling is widened. Final
CI and independent current-head review remain delivery gates.
Reproducibility policy sourceRevision:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.

Claim/type self-sweep: the first result derives a remainder from two structural
assumptions, not their truth; characterization is an iff; comparison asserts
pointwise predicate equivalence, not formation; greatestness is relative to an
inhabited fixed carrier; the joint certificate witnesses only its declared
mathematical rival. There are no changed attributed claims. Actual root delta
from base `13f1d8f2b3f96687248f7aa1a10e288a29a2a2eb`: open premises remain
90 (30 bare, 18 supported, 42 stated); cheapest route remains cost31; no change.
All actual ontology, substance, composition-as-identity, applicability and
modal/causal assumptions remain open. The existing modal decomposition theorem
is untouched; its overlap-extensional premise is not independently discharged
by conditional framework exploration. The successful attempt is recorded in
`corpus/attempts/supplementation-fusion-1050.json`.


PR #1052 explorer-only repair: CI run 42133243925 passed corpus/Lean but the
all-statement source-location test rejected the new raw core binding `Nonempty`.
The narrow source-index diagnostic identified only `STMT-INHABITED-CARRIER`;
this was not a wrong declaration or a Lean parsing/type/proof failure. The
installed pinned Lean4.35.0 source declares `class inductive Nonempty` at
`src/Init/Prelude.lean:839`. The explorer's existing inspected-core location
mechanism now links that exact release/path/line, alongside `WellFounded`;
unknown toolchains still receive no guessed location. A focused regression and
the original statement-resolution test both reproduced red before the fix;
all 9 source/site-state tests, TypeScript checking and focused lint pass after
the fix. No Challenge, theorem, vocabulary, corpus binding or proof input
changed, so the successful binding/Comparator/NanoDa evidence above is reused.
Final-head CI and current-head review remain required. This adds navigation
metadata, not a philosophical source record or verification authority.
