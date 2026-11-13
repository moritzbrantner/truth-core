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
`D(x,x)`, which the counterfactual reading may make trivially true. Encoding
the existence facts via a supplied `existenceFact : B → Atom` prevents the
formal proof from treating a being and the fact that it exists as the same
object. The map does not assert that different beings have different fact
tokens; a derivation of the strict edge still has its full burden.

## The positive argument, step by step

1. **Ground-theoretic order.** Fine's strict partial ground obeys transitivity
   in the formal PLG, and a PLG-consistent theory cannot derive a strict
   ground of an atom by itself. These are existing verified results in
   `TruthCore.Results.Modern.Fine.PlgDerivedRules` and
   `TruthCore.Results.Modern.Fine.StrictGroundAcyclic`.
2. **Existential interpretation.** For this selected family of existential
   dependence edges, the OPEN map above is assumed to be faithful. This is
   where real metaphysical argument must justify the application of the
   ground relation, rather than merely importing its formal laws.
3. **Suppose a reversal.** Let `x ≠ y`, `D(x,y)`, and `D(y,x)`. The map gives
   `Ex(y) ≺ Ex(x)` and `Ex(x) ≺ Ex(y)`.
4. **Derive the contradiction.** PLG transitivity gives
   `Ex(x) ≺ Ex(x)`. With consistency, that is impossible. Thus
   `D(x,y) → ¬D(y,x)` for distinct beings.

This new proof composes the **existing Fine result** into the unchanged
proposition `STMT-DISTINCT-BEINGS-NOT-MUTUALLY-DEPENDENT`; it supplies an
alternative conditional support, not a direct proof that all actual
counterfactual dependence is strict grounding. No regress or well-foundedness
assumption is needed, and no new argument for God's existence is asserted.

## Why this bridge is a philosophical claim, not a synonym

The strongest positive rationale is **constitutive explanatory direction**:
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

## Effect on the God-existence support graph

The new proof creates another way to support one of the **nine inputs shared
by the terminal-only calculation**. Its premises are consistency and faithful
strict-grounding interpretation, neither disguised as a definition. It does
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
  `TruthCore/Results/Causality/DependenceStrictGroundMap/{Challenge,Solution}.lean`.
