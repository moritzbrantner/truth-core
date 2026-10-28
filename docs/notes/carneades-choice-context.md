# Carneades: lawfulness, complete input and decision criteria

This is a bounded extension of the free-will section of
[the existing intake](carneades-frontier-intake.md), not a second handoff.
The source gives a definition fork; the formal tables below are explicitly
stipulated controls. No historical attribution or source claim is added.

## Readings and evidence limits

Read the entire public article,
https://www.carneades.org/post/over-two-thirds-of-americans-are-libertarians-about-free-will ,
with particular attention to **What Philosophers Mean By Free Will**, numbered
claims 1–3 and the following paragraph; also **Methodology Specifics**, response
options 1–3. The former presents determinism, freedom as doing otherwise, and
freedom's existence as an inconsistent triad; the latter explicitly offers
absence of coercion as an example of a changed freedom criterion. Neither
survey prevalence nor consistency of respondents establishes a metaphysical
premise. The article does not specify complete initial conditions or a law's
functional versus relational semantics. Those distinctions below are our
stipulations, not attributed readings.

Read the **complete** English `en-orig` auto captions of the public video
**What is Free Will? (Metaphysics)**, Carneades.org,
https://www.youtube.com/watch?v=KODJicKd5ps (357 seconds). Download SHA256:
`2a128be1bff287b6a02db0c99e5720074339a41f7d16c5f39b196b08e6dca3bd`.
Reproduce using the existing intake's `yt-dlp` command with this video ID.

- **00:22–00:43:** existence questions depend on what freedom means.
- **01:10–02:06:** triad and rejection of the doing-otherwise criterion as a
  possible response. **02:06–02:43** acknowledges different precise formulations
  of both determinism and freedom.
- **02:52–03:29:** hard determinism and compatibilism are distinguished by which
  claim is rejected; this is an introductory taxonomy, not a defense of either.
- **03:37–03:59:** the libertarian exposition describes breaking deterministic
  patterns/laws. Reject promoting this wording to a general thesis that all
  libertarian freedom violates laws. A law may itself allow multiple outcomes.
- **04:07–05:23:** announces companion arguments and distinguishes broad
  determinism from hard/soft variants; the narrator reports skepticism rather
  than presenting a decisive argument for any of the three positions.

Audio/slides are unverified, auto captions contain obvious transcription errors,
and no admissible `media_span` producer/export provenance was obtained. The VTT
hash identifies downloaded bytes, not a verified passage. The article has no
pinned `web_snapshot`. Accordingly there are no attributed claims; source
pinning/materialization remains necessary before formalizing an attribution.
`CARNEADES-FREE-WILL-ADEQUACY` preserves that boundary and the next research gap.

## Actual argument and rival controls

Reuse `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` and the exact theorem
`TruthCore.Results.Modal.SelectedEffectBridge.fixedConditionsStable`.
The generic clause in `ChoiceContext.Controls` feeds that theorem the ordered
pair `(law, input)`. It is a specialization/composition of the existing bridge,
not a new argument that PSR entails determinism or modal collapse.

The new finite table has three independent inputs in `History`: a Boolean law
selector, a prior preference, and an imposed constraint. The complete input of
the response table is `(preference, imposed)`. An imposed constraint forces the
`true` action. Without it, law `false` follows preference; law `true` reverses it.
Completeness here is exhaustiveness of the displayed function's arguments,
not completeness of a physical description. There is no opaque freedom atom.

| History | Law | Preference | Imposed | Action |
| --- | --- | --- | --- | --- |
| `actual` | false | true | false | true |
| `changedInput` | false | false | false | false |
| `changedLaw` | true | true | false | false |
| `constrained` | false | false | true | true |

`sameContextSameAction` proves that equal law and equal complete input force
identical action. `controls` consequently excludes an `Alternative` at every
history. Nonetheless there is an unconstrained actual history, a different
output with law unchanged but input changed, and a different output with input
unchanged but law changed. Thus neither equality may be discarded when using
cross-history variation to challenge the functional determinism encoded here.
The actual action also coincides with that of a constrained history, so its
value alone does not determine the modeled constraint status.

The second control uses **one identical relation**, `relationalLaw c a`, under
which imposed input requires action `true`, and unconstrained input permits
both `false` and `true`. The certificate explicitly verifies these two distinct
outputs at the *same* `input actual`. This is lawful nonfunctionality, with a
nontrivial restriction at constrained inputs. Reject equating nondeterminism
with law violation. The functional and relational laws are separate stipulated
interpretations; we do not combine their outputs as one model's laws or claim
physical realizability, probability distributions, agency or responsibility.

Strongest rival to an incompatibilist adequacy claim: perhaps freedom and desert
require an appropriate reason-responsive or ownership structure rather than
these fixed-input alternatives. Strongest rival to a simple compatibilist
adequacy claim: absence of this one imposed override may leave manipulation,
incapacity, compulsions or sourcehood unresolved. Neither rival is settled by
choosing a flag or by an LLM accepting a definition. No criterion is promoted
to a sufficient condition for freedom or responsibility.

## Premises, self-sweep and verification boundary

The certificate is closed: its generic transfer is universally quantified over
explicit hypotheses, and the controls use named finite witnesses. The result
has no ordinary premise statements. It has no route to the Catholic root;
root open-premise delta is exactly zero. No existing premise is added, removed,
or discharged; all libertarian/compatibilist adequacy and theological
applicability commitments remain open. #555 remains research-only.

The prose/type comparison is exact: `SameContext` fixes law and full modeled
input, `Alternative` existentially changes the resulting action, `Unconstrained`
means only `imposed=false`, the witness equalities describe these particular
records, and the relational law admits both Boolean outputs at the identical
specified input. Nothing is asserted about every unconstrained agent, moral
responsibility or actual physical laws. Definition and disambiguation records
link these distinctions and the reused output semantics.

Dossier inspected for `STMT-SELECTED-EFFECT-BRIDGE-CERTIFICATE` before work;
`ATTEMPT-CARNEADES-CHOICE-CONTEXT` records the attempt and rejected readings.
The shared persistent Lean service returned no diagnostics on the complete
combined module/proof content, SHA256
`48daeb35137b873750348f07c63667dc5b63ebe1f1730be71e96039a0d5602b0`,
preview revision `49b4589aa6744c91a6bc9adec13215d0e7245c9d`, session
`causal-harvest`. Initial elaboration took 0.745 seconds; the changed relational
control elaborated in 0.21 seconds without restarting a Lean session. This is
proof-edit feedback only. Canonical module build, binding, Comparator and
NanoDa evidence belong to the delivered revision's CI; interactive diagnostics
do not replace those gates.
