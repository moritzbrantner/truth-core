# Two coordinate frames, simultaneity and an additional present

## Question and fixed profile

Can one relation agree exactly with simultaneity in every frame, and does a
negative answer establish that there is no objective present? The bounded
certificate answers the first question for two explicitly supplied coordinate
frames. The second needs an independent physical/ontological bridge.

The analyst profile uses `Event := ℝ × ℝ` in units `c=1`. Its quadratic interval
is the actual Mathlib quadratic form `sq.prod (-sq)`, evaluated as `t²−x²`.
The pinned Mathlib has no dedicated Minkowski/Lorentz module; the implementation
uses `QuadraticMap.IsometryEquiv` and the ordinary product real module, not a
hand-rolled mathematical isometry or an external physics dependency. The
rational boost has `v=4/5`, `gamma=5/3`:

```
(t,x) ↦ ((5t−4x)/3, (5x−4t)/3).
```

The inverse uses plus signs. A direct ring calculation certifies the quadratic
isometry. `|x|≤t` is the supplied future cone, including zero; two elementary
linear-inequality arguments prove preservation in both directions. Linearity
then preserves this relation on event differences. This is an indefinite
quadratic interval, not a positive-definite norm or Euclidean metric.

The explicit events `(0,0)` and `(0,1)` are distinct and spacelike, with interval
`−1` for their difference. They have equal original times; the boosted times are
`0` and `−4/3`. Thus no relation can coincide exactly with both frame-time equality
relations. The original relation nevertheless witnesses a designated relation
that agrees with one frame and not the other. That witness is a relation in the
mathematical model, not a complete or established presentist ontology.

## Primary witness and defensible readings

`EINSTEIN-1905-KINEMATICS` materializes the complete §§1–3 from the Fourmilab
reproduction of the Perrett–Jeffery English translation (1923), electronically
edited by John Walker (1999). Live HTML was fetched twice identically. The fixed
2024-01-16 Wayback capture was also fetched twice identically and has exactly the
same selected text. The edition's footer explicitly acknowledges notation
changes and corrections to the 1923 translation; its §3 editorial note corrects
coordinate-axis/system labels. Those editorial details are not silently treated
as Einstein's original notation.

The existing HTML text extractor omits equation images. All three attributed
claims therefore use only materialized prose:

- §1 introduces a remote-clock synchronization convention, assumes its
  consistency and symmetry/transitivity, and defines event time by a local
  stationary clock synchronized with the same reference clock in that system.
- §2's conclusion about disagreement between stationary and co-moving observers
  on the rod-end clocks is conditioned on its relativity/light-speed principles
  and the §1 clock construction. It is not a claim that *every* simultaneous
  pair ceases to be simultaneous, including coincident events.
- §3 assigns two coordinate-time descriptions to the same event, motivates
  linearity through homogeneity and checks light-wave propagation. No image-only
  transformation equation is attributed through the extracted prose.

The rational boost is an independently specified mathematical control, not a
claim that this batch reconstructs the entire source's derivation or verifies
its empirical premises. German Wikisource was consulted for orientation; its
full-page render was rejected as the pinned witness because a generated-at
footer changed raw bytes. Its raw main page only transcludes subpages. No
attributed claim relies on that unpinned rendering. Fourmilab's legitimate
primary-translation witness, not model memory, supports the claims.

## Strongest replies and what is actually constrained

| Question | Tenseless/frame-relational reply | Additional preferred-present reply | What the certificate settles |
| --- | --- | --- | --- |
| Remote simultaneity | Use each frame's synchronized coordinate time. | Treat coordinate descriptions as physical representations while additionally selecting a preferred relation. | These two coordinate relations differ. |
| Objective present | A further present need not be posited for this description. | A primitive preferred foliation need not agree with every frame's time equality. | A relation matching one frame remains mathematically available; neither ontological reply is established. |
| Causal order | Preserve the supplied future cone, while spacelike time comparisons may differ. | A preferred relation may coexist with the same geometric cone. | The exact cone relation is preserved in both directions. No ordinary cause or ontic dependence is inferred. |
| Passage/A-properties | Add no A-property merely by choosing coordinates. | Defend a distinct tensed/passage interpretation. | No A-properties, becoming or truth-at-now semantics are encoded. |
| Physical justification | Defend the applicability of frame, clock and light assumptions empirically. | Defend any preferred structure and its empirical/metaphysical motivation. | The formal carrier and equations alone settle neither burden. |

A stronger bundle requiring one objective-present relation to equal the
simultaneity relation of **both** frames is incompatible with this model's
computed pair. A presentist need not accept that bundle. Conversely, a relation
can be designated in the model without thereby having an independently adequate
physical or metaphysical justification. Physical equivalence, empirical
indistinguishability and numerical event identity are different issues.

## Exact reuse and rejected transfers

Existing `HistoryTimeScope.Controls` handles quantifier ordering on a shared
history/time domain. It does not supply inertial transformations; a frame here
is not a different modal world or complete possible history. These coordinates
must not be substituted for `Ontic.Causes`, modal accessibility or actual
existence. The source's two descriptions concern the same event.

The Aristotle Physics IV.11 simultaneity/succession reading likewise supplies
no Lorentz transformation. Same-being/same-respect act/potency exclusion is not
the remote-event simultaneity relation tested here. No Aristotelian premise is
refuted by silently identifying them. Existing temporal-necessity and
past-bound controls remain separate; a real coordinate carrier does not prove
that an actual universe has an infinite past or no first event.

Rejected approaches: defining the preferred present to match every frame and
then calling presentism impossible; calling an indefinite quadratic isometry a
Euclidean metric isometry; inferring all causal ordering is frame-relative;
inferring physical actuality from the inhabited coordinate carrier; and adding
an empirical premise just because a proof needs it.

## Verification and remaining premises

`BOOST-SIMULTANEITY-CONTROLS` has no philosophical premise hypotheses: it is a
closed certificate about the fixed analytic profile, with all restrictions
visible in definitions. The event type is inhabited and the simultaneous pair
has distinct spatial coordinates; no empty-domain or coincident-event-only
control carries the result. There are no modal worlds or concrete-existence
predicates in this profile.

The Challenge was frozen before Solution proof search. Shared service version3
accepted combined exact source/Solution content (only a temporary `#print
axioms` added), SHA256
`9382b885fecc47b760abaeae3897108792168e05fc8c4a9309fa161de34af41b`,
workspace `/home/brantner/privat/truth-core-sprint-proof`, head
`f2544a0142304bf074112e7323cb5b8ab6e46840`, session `causal-harvest`.
There were no errors or warnings and only the allowed `propext`,
`Classical.choice`, `Quot.sound`. The informational axiom print is removed from
the canonical Solution. Final delivered-head CI owns build, binding,
Comparator and NanoDa; focused diagnostics are not advertised as those gates.

Actual intended/root-path premise change: **none**. Physical applicability,
clock/synchronization adequacy, any no-preferred-structure principle and any
connection to actual causal/metaphysical ontology remain independently open.
The next candidate is `RELATIVITY-PRESENT-APPLICATION`, not a declaration that
one temporal metaphysics has won.
