# Carneades frontier intake (2026-10-28)

Bounded owner-authorized source intake for #311/#312/#319/#320/#462/#467/#555.
Repository comparison: `6926980efb1961753212cf4a43249a774c2724f2`, branch
`research/carneades-intake`. This is a research note, not a source claim,
formalization, proof certificate or handoff tracker. No premise change.

## Access and fidelity boundary

The public PHIL230/PHIL231 course pages give outlines, not the arguments:
https://www.carneades.org/challenge-page/philosophy-of-religion and
https://www.carneades.org/challenge-page/ontological-argument . No login,
enrollment, payment or hidden content was used. Ordinary public YouTube captions
were available through the already installed `yt-dlp`, although web extraction
of the Kant watch page failed. The four video readings below use complete
English `en-orig` auto-caption files, read across the whole recording, not search
snippets. Audio/slides were not checked; obvious caption errors occur, including
names and technical vocabulary. Treat paraphrases as provisional readings of
Carneades's exposition, not authenticated historical claims about Hume, Kant,
Aristotle or Aquinas. Speaker attribution is to the channel's narrator, with no
claim to an identified individual speaker.

No passage manifest or attributed corpus claim is created. Before one is
created, obtain the existing `media_span` producer/export provenance, materialize
it, and check decisive wording against audio. Raw VTT hashes below identify the
consulted downloads only; they are **not** `span_sha256` or a successful
`source_evidence.py materialize` result. Full transcripts are not committed.
Reproduction (substitute each video ID):

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-intake.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=RF6GVgZgiWA'
```

## 1. Memberwise explanation versus whole-system explanation

Read: **Hume's Objections to the Cosmological Argument**,
https://www.youtube.com/watch?v=RF6GVgZgiWA .
Consulted VTT SHA256:
`5f24bf42ad2e42df0b7ea2b874d25f753ed18620042501d25488d85dc8653ee8`.

- **00:53–02:10:** the narrator presents the rival that explaining each of twenty
  portions of matter explains their collection, and extends it to the universe.
- **02:10–03:08:** reply: explaining chicken by egg and egg by chicken, or
  continuing indefinitely, fails to provide the satisfactory explanation of the
  whole process being sought. This is an explanatory-adequacy objection, not a
  demonstrated logical inconsistency of an active cycle or infinite chain.
- **03:12–04:04:** a conceivability argument against unrestricted causation is
  followed by objections: limited understanding can mislead conceivability;
  logical possibility does not by itself establish metaphysical possibility.
- **04:04–05:04:** a proposed rescue, attributed by the narrator to Mackie,
  distinguishes methodological usefulness of a causal principle from its
  ontological justification. The narrator's closing historical characterization
  of Hume at 05:04 onward is not reused; neither it nor the previous historical
  attributions has been checked against a primary witness.

**Strongest useful rival:** every demanded local fact may have an explanation,
while a further question about the inventory/history is either already answered
or requires a separately defended contrastive standard. **Strongest reply:**
local predecessor assignments leave the system's presence/profile open.
Neither speaker dissatisfaction nor an LLM's agreement establishes that standard.

**Reuse and gap:** `STMT-HISTORY-CONTRASTIVE-CONTROLS`, declaration
`TruthCore.Modal.HistoryContrastive.Controls`, is certified by
`TruthCore.Results.Modal.HistoryContrastive.controls`. It already separates
local coverage from contrast discrimination and even allows a stipulated
internal contingent discriminator. Thus reject any reading that this video
proves an *external*, *necessary*, *unique*, or *simple* explanation must exist.
The genuine remaining #311/#312 bridge is why the selected complete-history
contrast requires explanation, and which internal/circular explanations fail
that independently motivated adequacy criterion. A mandatory-external-explainer
axiom would merely choose the disputed answer. This recording offers a compact
rival/reply presentation, not that bridge's defense.

## 2. First Way objections: applicability, respects, and multiplicity

Read exposition: **The Unmoved Mover (Aquinas's First Way)**,
https://www.youtube.com/watch?v=-YFtBC9lJmo . Consulted VTT SHA256:
`4b9daa62b45a4a26abeb71ee1175a61210989517bdc4a4a23f38ea9c8fd7eb1a`.
Read companion: **Objections to St Thomas Aquians First Way (The Unmoved Mover)**
(title spelling as supplied), https://www.youtube.com/watch?v=XJzCYqiLWt0 .
Consulted VTT SHA256:
`60d2aef1ba0ba48ae2767abbdd408f18f30b776999562efd5ca61cb1fc17fe40`.

Exposition **03:07–04:01** qualifies act/potency exclusion by time, property and
respect; **06:32–07:51**, **10:22–10:53** assumes rejection of infinite regress
and passes to an unmoved pure actuality, then identifies it as God. This is no
independent defense of the no-regress premise or of extending independence in
one respect to the being as a whole.

Companion objections:

- **00:22–02:02:** proving a generic mover does not establish the biblical God;
  the narrator explicitly acknowledges that Aquinas offers further arguments.
  Preserve this qualification rather than presenting it as a refutation of
  those further arguments.
- **07:01–09:00:** a rod heated at one end and cold at the other is offered
  against act/potency exclusion and in favor of composite self-change.
  **09:00–10:14** adds machines. Reject reading the rod as both hot and not hot
  in the *same part/respect*; the example instead tests whether whole-object
  descriptions have erased relevant parts and respects. The original exposition
  itself supplies the same-respect restriction. Machines likewise do not show
  absence of all internal or external actualizers.
- **10:26–11:41:** the narrator separates conditional success in a gear-chain
  model from warrant for applying that model to real change. This is the
  strongest reusable methodological challenge.
- **11:44–12:28:** a hot bowl and cold water mutually change temperature;
  **12:51–13:12** uses a binary star analogy. These are proposed challenges to
  universal essential-series applicability. They do not demonstrate the
  metaphysical possibility of a causally closed two-object universe or answer
  existential conservation. Opposite effects can also concern different
  respects, so a graph cycle alone does not establish same-respect borrowed
  power or contradiction.
- **13:15–15:13:** infinity/motion analogies motivate suspending judgment rather
  than claiming a demonstrated infinite explanatory series. Convergence of
  subdivisions does not imply an essentially ordered causal regress exists.
- **15:15–17:39:** explicitly raises nonuniqueness, including two driving gears;
  the proposed identification with physical forces is offered abductively
  (**18:42–18:58**), not as a proved identity.

**Reuse:** `STMT-FIRST-UNMOVED-MOVER-IS-FIRST-BEING`, existing
`TruthCore.Results.Causality.PowerExistenceBoundary.powerExistenceBoundary`
and `.originalPowerBlocksEsseSupportIfItTransmits`; existing #319 audit at
`docs/power-existence-scope-boundary.md`. #320's
`STMT-PLURAL-FIRST-MOVERS-WOULD-DIFFER-IN-ACT` and
`TruthCore.Results.Case.Catholicism.Q11NatureUniqueness.godIsOneFromNature`
already expose additional uniqueness assumptions. Their old omission controls
must not be relabeled a new sourced physical model.

**Remaining inference:** defend essential causal dependence for the actual
respect under discussion, transport it to existential support of the *same*
individual if required, and supply the additional individuation/perfection
premises for uniqueness. Neither the examples nor the replies supplies that
transport. Strongest new intake value is a clear applicability objection and
concrete rival cases to audit against existing typed semantics, not a new proof.

## 3. Necessity and identification

Read: **Kant's Objection to the Cosmological Argument**,
https://www.youtube.com/watch?v=gqrRl-1UT70 . Consulted VTT SHA256:
`e7ef356f8c2445f29be9f05f73831502940742994ef3450ed7da1eb3790e4f51`.

**00:35–01:30** distinguishes inconceivable denial, all-possible-world existence,
and never beginning/ceasing. **01:34–03:38** argues for dependence on an
ontological argument; **03:39–04:16** challenges mere everlastingness;
**04:17–04:49** emphasizes that the identified necessary item has not thereby
been shown to be God rather than universe, Big Bang or consciousness.

Reject literal same-profile reading of **03:03–03:38** as both existence at
*every* possible world and absence at some possible world: the narration moves
between logical and metaphysical possibility. It requires separately defined
modal domains to become a coherent two-modality argument. Lack of contradiction
in conceiving a candidate is also not evidence it supplies an adequate intrinsic
reason. These are reading boundaries, not claims that all necessity arguments
fail.

**Reuse:** `STMT-KANT-COSMOLOGICAL-ONTOLOGICAL-DEPENDENCE` is already a more
carefully restricted primary-source reading about identification with
ens realissimum; do not broaden it to every cosmological proof on this video's
authority. `TruthCore.Results.Kant.CosmologicalInference.IdentificationNeedsBridge.identificationNeedsBridge`
already supplies the identification control. `STMT-TEMPORAL-MODAL-DEPENDENCE-CONTROLS`
and `TruthCore.Results.Modal.TemporalHistoryControls.controls` already separate
everlastingness from modal necessity. The further source gives no new necessity,
simplicity, uniqueness or actuality-selection bridge.

## 4. Free will and the modal-collapse boundary

Full public article read:
https://www.carneades.org/post/over-two-thirds-of-americans-are-libertarians-about-free-will ,
section **What Philosophers Mean By Free Will**, all three numbered claims and
the following paragraph. It presents an incompatible triad: deterministic laws,
freedom as being able to do otherwise than those laws determine, and existence
of free will. Hard determinists reject existence, compatibilists reject that
freedom criterion, libertarians reject determinism. The survey statistics are
not evidence for any premise's philosophical truth.

**Reuse:** `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE`;
`TruthCore.Results.Modal.SelectedEffectBridge.fixedConditionsStable` and
`.selectedEffectNecessary` already distinguish fixed complete conditions plus
an exact response law from mere local uniqueness or a necessary source.
Different accessible worlds alone do not witness doing otherwise with the same
complete conditions/laws. The article's generic triad does not show that divine
simplicity entails a necessary rigid act or strict invariant effect efficacy
(#555), and does not show PSR alone entails determinism (#312).

A search lead titled *The Principle of Sufficient Reason Proves Determinism,
or That There is No Contingency*, https://www.youtube.com/watch?v=zgu0M6YYp2s ,
was checked by actual metadata and full auto captions. Its channel is
**Oppositum**, not Carneades.org. It was rejected from this site-specific intake;
no Carneades attribution or new historical-source campaign is inferred.

## Priority and next concrete step

1. Reuse the Hume companion's local/whole and methodological/ontological
   distinction to sharpen #311's disputed adequacy criterion. Source pinning
   would support attribution only; it would not justify the criterion.
2. Audit the bowl/water and rod cases against existing respect-indexed
   dependence and power/existence controls; preserve them as applicability
   objections rather than alleged decisive formal counterexamples.
3. Reuse the explicit multiplicity and necessity-identification objections
   in #319/#320. Their missing premises are already visible; do not duplicate
   those controls or turn scientific-force analogies into established ontology.
4. Treat the free-will triad as background orientation for #462/#555 only.
   The current fixed-condition/output bridge is materially more precise.

Dossiers inspected: `STMT-HISTORY-CONTRASTIVE-CONTROLS`,
`STMT-FIRST-UNMOVED-MOVER-IS-FIRST-BEING`,
`STMT-PLURAL-FIRST-MOVERS-WOULD-DIFFER-IN-ACT`,
`STMT-KANT-COSMOLOGICAL-ONTOLOGICAL-DEPENDENCE`, and
`STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE`. No Lean command was run, no theorem
or source claim added, and no target/root premise added, removed or discharged.
