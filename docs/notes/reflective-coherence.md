# Reflective coherence: objective duties and worldview selection

**Status:** owner-proposed conditional framework, not a sourced historical claim
and not an established objective epistemic duty. Formal home:
`TruthCore/Logic/ReflectiveCoherence.lean`.

> If I have an objective duty to believe in a consistent worldview, I should
> believe in a worldview consistent with that duty and its necessary
> implications.

The attractive principle contains more than one logical step. The important
distinction is between a *worldview that contradicts itself* and an *internally
consistent worldview that is false about an external objective duty*. The latter
can be a genuine epistemic error without being a formal contradiction.

## Three registered consequences

1. **Semantic boundary** (`STMT-REFLECTIVE-COHERENCE-BOUNDARY`,
   `LOGIC-REFLECTIVE-COHERENCE-BOUNDARY`): with a fixed interpretation of claims
   and negation, if a worldview entails the negation of a duty-content, it is
   incompatible with that content. If it **also accepts the duty-content**, the
   worldview itself is inconsistent. If the content is **true at the actual
   world**, the worldview is false at that world. Compatibility with a content
   persists for every semantic implication of the content.
2. **Conditional reflective duty** (`STMT-TRUTH-DIRECTED-REFLECTIVE-DUTY`,
   `LOGIC-TRUTH-DIRECTED-REFLECTIVE-DUTY`): if the duty-content is true at an
   actual world and an *additional truth-directed epistemic selection norm*
   requires every worldview one ought to adopt to be true at that world, then
   the selected worldviews are internally consistent and jointly compatible
   with the duty and all its implications. The existing
   `SelfApplication.Norm.Holds` schema captures the consistency and
   compatibility norms. The truth-directed bridge is not derived.
3. **Limits** (`STMT-REFLECTIVE-COHERENCE-LIMITS`,
   `LOGIC-REFLECTIVE-COHERENCE-LIMITS`): finite controls demonstrate that a
   policy can require only consistent worldviews even while selecting one
   which denies a duty-content true at the designated actual world. Another
   finite control exhibits a consistent worldview that does not explicitly
   include a consequence it entails. Logical coherence is therefore not
   a principle of psychological or epistemic *logical omniscience*.

All three results are premise-free *conditional* semantic statements in their
Lean types. That does **not** mean that their framework antecedents, such as the
objective duty's truth or the epistemic selection bridge, are proven true.
They introduce no new proof of theism, the PSR, revelation, or Catholicism.

## Precise interpretation

- A `Worldview` is a collection of explicitly included claim-contents, not a
  person or a full account of what a person implicitly recognizes.
- `Consistent` means there is a common model of its contents. It need not be
  true at the actual world.
- `Entails` means true in every model of the worldview, relative to the fixed
  semantic profile. A worldview can entail an unendorsed claim.
- `Compatible` means the worldview and an additional claim have a common model.
  It does not require accepting the additional claim, nor prove it true.
- `OughtAdopt` is an uninterpreted **normative** selection predicate. The
  model has no hidden assumption that an objective epistemic duty exists or
  that a duty about consistency entails a duty about believing every truth.
- `TruthDirected` says *all contents* of every selected worldview are true at
  the designated actual world; it is deliberately strong. A weaker epistemic
  permission principle (e.g., rational permissibility under limited evidence)
  would require a separate bridge and different results.

### Why the strong inference requires more than consistency

Let `d` say “there is an objective duty to hold coherent beliefs.” Even if `d`
is true at the actual world, the worldview `{¬d}` is syntactically coherent and
is satisfiable in the two-world control. It is mistaken at the designated
actual world but does not assert `d ∧ ¬d`. The additional inference

> There is an objective duty to hold a consistent worldview; **therefore** I
> ought to adopt only worldviews compatible with that objective duty.

is not valid just from *consistency* as its norm. One must supply, for example,
a normative truth-directedness bridge, an independent duty to acknowledge
known objective epistemic norms, or a justified self-application commitment.
This project currently registers the first as a conditional experiment, not
as a settled fact. In particular, a duty to be rational is not automatically
a duty to believe everything entailed by one's beliefs.

## Relation to the broader inquiry

The [internal adoption reasons analysis](self-undermining-views.md#internal-reasons-to-adopt-a-view)
asks which reasons an interpretation admits for adopting a view and distinguishes
epistemic reasons to believe it from moral reasons to adopt it in practice.

The existing `TruthCore/Logic/SelfApplication.lean` handles norms,
self-application, and counterexamples; this module instantiates its norm schema
for worldview selection. `TruthCore/Explanation/PSRSelfApplication.lean` makes
a separate distinction between demands for reasons and the ontic existence of
reasons. Neither distinction authorizes a direct bridge from objective epistemic
norms to an explanation of their metaphysical ground.

To use reflective coherence in an argument about God, future work must identify
and separately test at least:

1. **The norm's existence and content:** whether objective epistemic duties
   obtain, in which sense of objective, and how they are knowable.
2. **Normative bridge:** whether the truth of such a duty imposes a duty to
   select worldviews compatible with it, and under what epistemic conditions.
3. **Discriminating consequence:** whether the duty's existence or best
   explanation favors theism over nontheistic normative realism, constructivist
   or other serious alternatives; and which attributes of God, if any, follow.

Until these are established, the result is a rigorous consistency and selection
filter—potentially valuable to compare complete worldviews—but not evidence
by itself for God's existence, uniqueness, necessity, goodness or personhood.
