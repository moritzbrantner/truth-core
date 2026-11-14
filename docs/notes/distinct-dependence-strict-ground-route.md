# A scoped strict-grounding argument for nonmutual existential dependence

Date: 2026-11-13. This note elaborates **premise 2** of the nine shared
terminal-input combinations for God-existence support. The formal route is
recorded in `specs/existential-dependence-strict-ground.toml`; existing direct
acceptance of the premise remains available.

## The three different relations

Let `x` and `y` be **beings**, `Ex(x)` and `Ex(y)` their respective **existence
facts**, and `S` the assumptions of a Fine-style pure logic of ground (PLG).

1. `D(x,y)` is Truth Core's existing counterfactual **dependence for being**:
   without `y`, `x` would not be. This is stipulated as a relation on beings;
   its interpretation allows impossible counterfactual antecedents.
2. `StrictlyGrounds S Ex(y) Ex(x)` means that the existence fact of `y` is
   derivably a **strict partial ground** of the existence fact of `x` in Fine's
   PLG, relative to `S`. The calculus's consistency and derivability are
   syntactic, not automatically ontological.
3. `PriorSimply y x` is the project's selected **simple metaphysical
   priority**. It is neither counterfactual dependence nor strict grounding
   by definition. In particular, causal or temporal precedence and
   explanatory grounding should not be collapsed into one predicate.

The selected mapping is an **OPEN philosophical bridge**:

```text
For all distinct x,y: D(x,y) → StrictlyGrounds S Ex(y) Ex(x).
```

It is a directional implication, not an equivalence. It says nothing about
`D(x,x)`, which the counterfactual reading may make trivially true. The map
does not assert that different beings have different labels.

### What the Lean type actually encodes: a structural surrogate

In the theorem, `S` and `existenceFact : B → Atom` are arbitrary parameters,
and the atoms are uninterpreted (`DEF-FINE-PLG-STRICT-PARTIAL-GROUND`;
`DEF-FINE-PLG-DERIVABILITY`: "derivability says nothing about what actually
grounds what"). The formal content of the premise bundle is therefore
**structural**: distinct-step `D` embeds, under some labelling, into the strict
partial ground order of some consistent PLG theory. Nothing in the type says
that the atoms are existence facts, that the edges are actual or faithful
grounding, or which kind of ground is meant. Writing `Ex(x)` for
`existenceFact x` is the **intended reading**, an OPEN interpretation outside
the type. The labelling keeps beings and atoms as different types, but it does
not make the atoms existence facts.

The bundle is **strictly stronger than the target**.
`mapForcesDistinctDependenceAcyclic`
(`TruthCore/Results/Causality/DependenceStrictGroundMapStrength/`) verifies
that consistency plus the map already force distinct-step `D` to have **no
finite cycle**, not only no 2-cycle. The formal warrant for the map is
therefore a warrant for the acyclicity of `D`, and any rival who denies
nonmutuality also denies acyclicity. This note does not verify, and nothing
relies on, two further claims:

- that the pulled-back relation is well-founded when `Atom` is finite (the
  challenger's observation, from `consistentStrictGroundAcyclic`);
- the converse, that every acyclic `D` admits such a consistent theory.

### Which "ground": the selected sense and the open readings

Disambiguation `23dd6f32-b456-4963-adb3-7befbf0dc4fb`
(DEPENDENCE_FOR_BEING_VERSUS_STRICT_GROUND) records the senses each term takes:

- `D` takes sense 1, `DEF-DEPENDS-FOR-BEING`: efficient-causal counterfactual
  dependence of an effect on its agent cause (ST I q.44 a.1 ad 2). Its paradigm
  is "the light in the air depends on the shining sun".
- "Ground" takes sense 2 only: Fine's formal strict partial ground on
  uninterpreted atoms.
- The argument passes from sense 1 to sense 2 only through the OPEN map
  premise, which is listed as a `sense_bridges` premise.
- The `controls` argument (missing map) shows that the two senses do not mix
  without that premise.

The theorem selects **no** metaphysical reading of the atoms. Two sibling
interpretations of the map remain open and untyped:

- **(a) Constitutive/metaphysical ground of existence facts.** This is Fine's
  non-causal metaphysical explanation, and it is the reading the rationale below
  appeals to. On it, the definition's **own paradigm edge is not covered**: the
  sun's existing is not standardly a partial ground of the light's existing. The
  light's existence is grounded in its constituents, and the sun is its cause.
  So the map would have to be restricted to a non-causal relation of receiving
  esse, not stated for the broad `D`.
- **(b) Natural/causal-production ground.** Here PLG is applied as the logic
  common to all grounding relations. On this reading the paradigm edge is
  covered, but the "constitutive explanatory direction" rationale does not
  apply. The map's warrant then reduces to the asymmetry of efficient causal
  dependence for being (compare `STMT-EFFICIENT-CAUSE-NOT-DEPENDENT-ON-EFFECT`),
  strengthened to acyclicity.

Neither reading is preferred by the formal result. A typed formalization of
either reading would need its own definition and Lean declaration: for (a), a
non-causal existence-fact grounding relation; for (b), a causal ordering of
existence facts. This is the precise next step for the interpretation.

## The positive argument, step by step

1. **Ground-theoretic order.** Fine's strict partial ground obeys transitivity
   in the formal PLG, and a PLG-consistent theory cannot derive a strict
   ground of an atom by itself. These are existing verified results in
   `TruthCore.Results.Modern.Fine.PlgDerivedRules` and
   `TruthCore.Results.Modern.Fine.StrictGroundAcyclic`.
2. **Existential interpretation.** For this selected family of existential
   dependence edges, the OPEN map above is assumed. Formally this is only the
   structural embedding. Its intended reading, that the edges are faithful
   grounds of existence facts, is a further OPEN interpretation. This is where
   real metaphysical argument must justify applying the ground relation,
   rather than merely importing its formal laws.
3. **Suppose a reversal.** Let `x ≠ y`, `D(x,y)`, and `D(y,x)`. The map gives
   `Ex(y) ≺ Ex(x)` and `Ex(x) ≺ Ex(y)`.
4. **Derive the contradiction.** PLG transitivity gives
   `Ex(x) ≺ Ex(x)`. With consistency, that is impossible. Thus
   `D(x,y) → ¬D(y,x)` for distinct beings.

This new proof composes the **existing Fine result** into the unchanged
proposition `STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT`; it supplies an
alternative conditional support, not a direct proof that all actual
counterfactual dependence is strict grounding. The **proof** uses no regress or
well-foundedness assumption. The **premise bundle**, however, commits to the
acyclicity of distinct-step `D` (see above). No new argument for God's
existence is asserted.

## Why this bridge is a philosophical claim, not a synonym

The strongest positive rationale, on reading (a) above, is **constitutive
explanatory direction**:
an existence fact genuinely receives its being from another fact, and the
source does not in turn receive that very existential actuality from the
effect. In that sense dependence marks an explanatory ordering rather than
mere correlation. Aquinas's *In V Metaphysicorum* lecture 13, nn. 15–18,
supplies source-backed conceptual support for priority's directional
dependence **when an order of prior and posterior is already given**. The
source does not establish that every counterfactual dependence pair falls
under such an order.

The gap is real. Ordinary necessity of co-existence does not orient an
explanation: two essentially inseparable but distinct constituents might
each be absent if the other were absent. On that broad counterfactual reading
`D(x,y)` and `D(y,x)` can both be true, while neither is a strict ground of
the other's existence. This is a **substantive scope alternative**, not a
merely conceivable unspecified objection. Any blanket identification of
counterfactual dependence with strict grounding would incorrectly rule it
out by definition. Likewise, explaining why a particular quality of a thing
obtains is not automatically explaining the existence of its entire bearer.

For the intended Thomistic explanatory sense the burden is now precise:

- Specify which existence facts actually receive esse from which sources,
  and in which respect. A separate same-respect source-dependent relation may
  be preferable to the current broad `D`.
- Defend the faithful **strict** interpretation. Weak grounding, correlation,
  essential co-instantiation and mere modal co-existence do not suffice.
- Show that the selected PLG assumptions are consistent and appropriate for
  actual existential facts, not just formally non-explosive.
- Transport the result to the selected `PriorSimply` only through a separate
  priority bridge. Neither this proof nor Aquinas's quoted order criterion
  defines that transport.

## Rivals to the map premise

Each rival names the target, the mechanism and its independent
justification. The two published rivals were supplied by the semantic
challenge on PR #1600. Their attribution is deferred: the cited texts have not
been materialized or read here, so they are recorded as navigation, not as
verified source claims.

| Rival | Target | Mechanism and justification | Price / standing |
|---|---|---|---|
| Modal co-existence (above) | Map on the broad counterfactual `D` | Essentially inseparable distinct constituents satisfy `D` both ways while neither strictly grounds the other's existence | The map must be restricted to oriented, source-dependent edges; still unresolved |
| Symmetric metaphysical dependence: E. Barnes, "Symmetric Dependence", in Bliss & Priest (eds.), *Reality and its Structure*, OUP 2018; N. Thompson, "Metaphysical Interdependence", in Jago (ed.), *Reality Making*, OUP 2016 | The map read as genuinely explanatory (reading (a)), and the strictness of grounding itself | Published positive arguments that some constitutive dependence is mutual (for example, positions in an ante rem structure). Such edges cannot be represented in any consistent strict-ground theory | If those cases are genuine dependence for being, the map fails on them. Defending the map requires either rejecting the cases or restricting `D` to a non-symmetric source relation. Unresolved; no refutation recorded |
| Vacuous counterpossibles (Lewis/Stalnaker semantics, defended by Williamson) | The map on `D` as `DEF-DEPENDS-FOR-BEING` defines it, "including where the antecedent cannot be realized" | On vacuist semantics, "if `y` were not, `x` would not be" is vacuously true whenever `y` exists necessarily. So any two distinct necessary beings mutually `D`-depend, and the map plus consistency then implies that `B` contains **at most one necessary being** | The map depends on a **non-vacuist counterpossible semantics** for `D`, or on a domain restriction (for example, excluding necessary abstracta from `B`). `DEF-DEPENDS-FOR-BEING` does not currently say which semantics it uses. This is a recorded dependency of the map, not a refutation |

No substantive objection to the formal validity of the derivation was
identified.

## Checked omission controls

The Lean `controls` theorem records two populated interpretations using the
distinct beings `true` and `false`:

1. **Without consistency:** `S = Set.univ` derives every ground sequent, so
   even wholly mutual `D` satisfies the formal dependence-to-ground map.
2. **Without the map:** the existing Fine infinite-descent construction
   supplies a consistent PLG theory while the unconstrained `D` is wholly
   mutual. The chosen theory simply does not interpret the relation.

These controls establish that the two inputs perform different work. They
do not prove either open input about metaphysical reality. They also prevent
the superficially attractive but invalid move of pointing to a partial-order
theorem and calling all ontological dependence a partial order.

**Nonvacuity.** `nonvacuity`
(`TruthCore/Results/Causality/DependenceStrictGroundMapStrength/`) gives one
joint formal model of the whole support bundle with a nonempty `D`:

- the consistent Fine infinite-descent theory over `Nat`, which derives `n+1 ≺ n`;
- the identity labelling;
- `D x y` iff `y = x + 1`, which has the distinct edge `0 → 1`.

So the bundle is not satisfied only by an empty `D`. This is a formal
interpretation only. It says nothing about real beings, and the model's
infinite descent is an incidental property of this witness.

## Effect on the God-existence support graph

The new proof creates another way to support one of the **nine inputs shared
by the terminal-only calculation**. Its premises are PLG consistency and the
structural strict-ground map. The map's reading as faithful grounding of
existence facts stays a further open interpretation. Neither premise is
disguised as a definition. It does
not replace the separate unrestricted independence-to-separability premise,
which faces the concrete necessary-being counterexample investigated in the
parallel replacement work. It does not automatically change the count of
premises that remain open or certify the theological conclusion.

**Next proposition:** `STMT-PRIORITY-REQUIRES-NONMUTUAL-DEPENDENCE`. In the two
root-facing consumers that only use `PriorSimply y x → D(x,y)`, first derive
and register a weaker sibling. Investigate whether actual causal/explanatory
priority suffices for that implication without the full reverse-dependence
negation; preserve the stronger original for the consumers that genuinely
need its other half. Next, examine the positive separation witness for the
existing independence premise only in the local context where it is used.

### Source and proof locators

- Fine, *The Pure Logic of Ground* (2012), §§2–3; formalized rules in
  `TruthCore/Modern/Fine/PureLogicOfGround.lean`; formal strict-ground results
  in `TruthCore/Results/Modern/Fine/StrictGroundAcyclic/Solution.lean`.
- Aquinas, *In V Metaphysicorum* lecture 13, nn. 15–18; consulted source and
  limits described in `docs/notes/priority-independence-logic-support-investigation.md`.
- Existing nine-premise research baseline:
  `docs/notes/nine-premise-support-investigation.md`.
- Current new formalization:
  `TruthCore/Results/Causality/DependenceStrictGroundMap/{Challenge,Solution}.lean`;
  strength and nonvacuity results in
  `TruthCore/Results/Causality/DependenceStrictGroundMapStrength/{Challenge,Solution}.lean`
  (spec `specs/existential-dependence-strict-ground-strength.toml`).
- Sense record: disambiguation `23dd6f32-b456-4963-adb3-7befbf0dc4fb`.
  Interpretation, rivals and next tests:
  attempt `1020b663-7fe1-42d2-8b0c-8a767607a1ce`.
