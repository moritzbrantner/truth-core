# Causal dependence: support for three common terminal premises

Date: 2026-11-13. Frozen comparison: `03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`.
Context: [God-existence support formula](god-existence-support-formula.md).

This investigation preserves the existing premises and asks what could warrant
them. It identifies a useful connection to an existing strict-grounding result,
specifies a sufficient modal bridge, and separates an esse-specific causal route
from the broader efficient-cause premise. The proposed bridges below are draft
specifications for review, not registered propositions or newly verified
theorems. No definition, source claim, Lean declaration, or proof status changes.

## 1. Targets and present assessment

Write `D x y` for the frozen `DependsForBeing x y`, `W x y` for
`CanBeWithout x y`, and `E c x r` for `EfficientlyCausesIn c x r`.

| Common premise | Exact existing content | Provisional warrant and best next route |
|---|---|---|
| P1, `000e1f65-6e74-5519-bbf3-300d5f61ada8` | `∀ x y, D x y → ¬ W x y` | Strong prima facie warrant for an essential, source-specific existential prerequisite. The frozen counterfactual sense still needs a bridge to the full admitted possibility range. Section 4 specifies one through persistence of dependence and centering. |
| P2, `0f49d71e-09e6-5a9c-b7e7-e0e9b8fe769c` | `∀ x y, x ≠ y → D x y → ¬ D y x` | Strong motivation for strict explanatory dependence; numerical distinctness and existential coimplication alone do not supply strictness. Section 5 connects an explicit strict-grounding interpretation to an existing PLG nonreversal result, without assuming well-foundedness. |
| P8, `c0d99549-799c-5a01-9b59-75fe88550b26` | `∀ c x r, E c x r → D x c` | The received-esse/conservation reading supplies a substantive conditional rationale. The frozen quantifier covers every respect of causing the same bearer, so esse-specific support does not discharge it. Section 6 gives the narrower existing route and the exact additional export needed for P8. |

All three remain open, supported analyst premises. That status does not make
their direct warrant worthless, and developing a derivation does not replace
the option of accepting a premise directly after considering its meaning and
grounds. Conversely, a plausible narrower interpretation cannot establish the
unchanged broader proposition. No requirement of independent or disjoint
support trees is imposed.

## 2. Semantic contract and evidence reviewed

The controlling definitions are:

- `bf26b9b2-41ed-55b0-9557-dae90ab9b81f`, dependence for being: x would not be if
  y were not, including the q.44 impossible-antecedent application. Its Lean
  parameter is a supplied binary relation. Neither asymmetry nor transitivity
  is built in. Self-dependence is compatible with this counterfactual reading.
- `d0b06beb-e8cb-5cb8-af2f-bc7f8cc004b2`, being-without: a real possibility of
  x being while y is not. It is a separate supplied relation.
- `69c0b23e-54c7-57a1-871f-839c6e5514c6`, `EFFICIENT_CAUSING_2`: c here and now
  efficiently causes **x's being r**. It does not stipulate that every such c
  causes the existence of x. The relation is also distinct from `CausesIn`.
- `56989bd0-a232-56ea-9093-c89350effff4`, direct per-se conservation of esse:
  the source account includes continuing productive dependence. The later
  typed `SustainsBeing` candidate deliberately omits that dependence clause.
  Its name or time indexing cannot supply the missing implication.

The `related` and `dossier` CLI reports were inspected for every target before
proposals. The relevant arguments, result records, and Solution bodies were
then read. The two first targets had no attempts in this baseline; P8 already
had an extensive investigation. The filtered orphan report identified the PLG
results as presently disconnected from root paths; the connection proposed
here is not yet a new graph edge.

### Primary sources actually read

Selected existing witnesses were materialized successfully and their complete
selected text read: `AQUINAS-ST-I-Q44-A1` (Latin article),
`AQUINAS-ST-I-Q104-A1-EN` (English article), and `AQUINAS-IN-METAPH-V-L13`
(Latin lecture, including paragraphs 15–18). These remain the existing source
records. The following source summaries specify their scope.

| Reading and existing evidence | What the passage contributes; limits |
|---|---|
| [ST I q.44 a.1](https://www.newadvent.org/summa/1044.htm), ad 2; claim `3ed36bec-27f4-5c77-93d5-3b6724d65204`, source statement `7673ebac-f30c-5960-8a4a-d779db4b14e1` | Aquinas gives a dependence rationale for efficient causality even for a necessary effect, explicitly allowing impossible conditional terms. The main article's participated-being argument presupposes earlier divine simplicity and unity claims. This is neither an independent proof of God here nor a vacuous material-implication argument. It does not supply every semantic dictionary from cause to modal or ground relations. The materialized Latin controls the reading; the linked English is corroboration/navigation. |
| [ST I q.104 a.1](https://www.newadvent.org/summa/1104.htm), body and replies; claims `40aefb2e-c9b3-5bb1-8802-96bbc4e2ed83` and `da9c82ed-e886-5335-81c3-cebad9b27345` | Dependence follows the respect in which the agent causes. Causing becoming differs from causing being; the builder and retained heat illustrate the distinction. Direct conservation continues the giving of esse, without repeated creation by motion or time. This positively motivates esse-specific dependence. The article supplies neither a general transfer from a determination to its bearer's existence nor a neutral experimental adjudication between conservation and existential inertia. |
| *In Metaphysicam* V, lect.13, especially n.18; claim `95f41960-baf4-58ad-ba7f-b11b2f439f7c`, statement `489711d5-3589-5e33-997a-4ba8bce1f492` | The argument concerns pairs already ordered as prior and posterior; its being-without qualification is “in some way,” with generation/corruption examples. The passage motivates a directed dependence account of priority. It neither quantifies over every pair of distinct beings nor identifies its dependence with the frozen counterfactual relation. |

Two further primary texts were read from the author's public uploads. They
are current research readings, not new pinned corpus claims:

- Fine, [*Essence and Modality*](https://www.academia.edu/8908669/essence_and_modality),
  author draft headed June 1992/revised February 1993, opening discussion and
  singleton example: an essential existential condition implies corresponding
  necessity, while mere necessary coexistence does not determine the direction
  or source of an essential connection. The Socrates/singleton comparison
  explicitly separates these questions. Draft section incipits, not assumed
  journal pagination, locate this reading.
- Fine, [*The Pure Logic of Ground*](https://www.academia.edu/8908730/the_pure_logic_of_ground),
  §§1–2, printed pp.3–7: strict ground excludes the relevant weak reversal;
  weak ground can represent explanatory equivalence. The paper distinguishes
  **strict partial** from **partial strict** ground; they are not interchangeable
  in the mixed transitivity rule. The reading corroborates the existing
  `FINE-PLG-1-2` bibliographic passage and claim
  `092c0769-d552-5860-889e-6bcf7b0f4aa6`. It does not upgrade that record to a
  hash-pinned witness. The canonical NYU PDF fetch failed; no unread PDF is
  attributed here.

### What is new relative to the earlier causal investigation

[Causal transitivity 1399](causal-transitivity-1399.md), attempt
`56ae2547-ae69-46f4-93b5-4c8ee786ed13`, already investigated received actuality,
the becoming/being distinction, existential inertia, impossible absence,
same-bearer identity, and the all-respects scope problem. The present source
reading corroborates those findings. It is not a new discovery that a heater's
causing heat does not by that fact explain the bearer's esse.

The additional work here is: (i) an exact sufficient P1 package that exposes
where essentiality must enter; (ii) a concrete connection from P2 to the
existing PLG nonreversal theorem, with its consistency and interpretation
requirements; and (iii) an explicit export package showing what the already
available esse-specific route would need to conclude the unchanged P8.

## 3. Reusable results and their full premise packages

These are existing registered results whose records and relevant Lean bodies
were inspected. No fresh Comparator or Lean execution is claimed.

| Result | Complete premises relevant here | What it actually concludes |
|---|---|---|
| `972ed7e5-098f-5ca6-9685-98d2cee48db8`, `Round2PerfectionPrimacy.efficientCauseNotDependent` | P8; `NothingIsEfficientCauseOfItselfReading` (`8b2561cd-3743-536d-a110-3352fdb0c6b9`); P2 | An efficient cause does not existentially depend on its effect. It consumes P2 and P8; it cannot establish them without circularity. |
| `47957c28-218a-58e4-94e4-5220a0c45795`, `Round2PerfectionPrimacy.nonmutualDependenceSuffices` | P1; independence allows being-without (`8ab3d114-d6e2-5f6d-805b-ae901f56d39b`); priority by being-without (`97fa3a0b-eb23-5fb1-9741-c1f09fb72206`) | Nonmutual dependence suffices for simple priority. No proof of P1 is supplied. |
| `695c2113-50b7-5b6c-ab51-e3cc02526d99`, `CausalMapsBatch1.efficientCausePrior` | P8; efficient cause independent of effect (`47b151ca-f500-5a7c-80d4-33bb90247ee3`); nonmutual dependence sufficient for priority (`bf93f259-29b4-53df-ae5b-ac7f522ea33d`) | Efficient causes are simply prior. It cannot be used backwards to justify its own dependence premises. |
| `db9175af-5a90-5cb2-b3e0-b8e25537be88`, `Round2Grounding.esseCauseGroundViaDependence` | Esse causes exist at the selected world (`c99f9d23-3f05-5c3c-9279-44a59e445a14`); esse causes are concrete (`82eeeb3c-b96d-5483-b1ac-f6059ff02211`); a distinct esse cause is depended on (`2068f91c-1eeb-5dbb-a71a-f7b6a12bb495`); actual concrete dependence is grounding (`2e248016-f8bf-5d8a-931e-7f9ebbb13e42`) | For actual concrete x, a distinct cause c of x's esse is actual, concrete, and a ground of x. All four premises remain explicit. Neither `CausesIn`/`EfficientlyCausesIn` identity nor an all-r extension follows. |
| `92c24bb5-763e-55d0-90b1-ef53d0bd0ab6`, `Modern.Fine.StrictGroundAcyclic.consistentStrictGroundAcyclic` | The corpus argument has no external premise statements because the conclusion itself universally quantifies the sequent theory S and **assumes `Consistent S`**. | No derivable finite strict cycle; no strict ground with its weak reversal; well-foundedness only if the atom type is finite. The theorem does not prove a selected S consistent or interpret actual dependence as ground. |

The fourth row is a useful existing route around an unnecessarily broad causal
interface, not a proof of P8. Its second registered variant,
`9783ec19-a74e-4198-8217-cc4d7175709f`, replaces the unscoped concreteness
premise with a separately derived existence/concreteness calibration; it also
does not discharge the esse-dependence premise.

The PLG theorem's finite-cardinality part is unnecessary for P2. Result
`fbc592d0-8fc4-5ac9-97f3-9302f3241d57`, statement
`73707346-9ddf-5c21-92d7-952739a9dc2b`, supplies an existing consistent PLG
infinite-descent example. Thus using nonreversal here does not silently import
termination or a first ground.

Other tempting shortcuts fail on scope. `Round2Grounding.asymmetricFromWF`
concerns a supplied grounding relation among actual concreta; it is not the
global P2. `asymmetricViaDependence` assumes dependence asymmetry, rather than
proving it. The global `DependenceForBeingAsymmetric` statement
`da8e6b60-4dab-5858-9c8d-f6e84c821970` even excludes self-dependence; it cannot
replace the deliberately distinct-only target without a sense change.

## 4. P1: from counterfactual dependence to essential absence exclusion

### Positive rationale

For a source that is an essential prerequisite of this very being, retaining
the being while removing that source violates the account of what the being
is. This is a substantive reason to accept a scoped P1: it connects an
independently specified identity or essence condition with real possibility.
It is stronger than the observation that the source usually accompanies the
effect, and differs from saying that any source of the same kind would do.

An illustrative package is a singleton under an ontology in which its
particular member belongs to its essence and an existing set's members exist.
Those identity and existence principles yield the relevant inability to exist
without that member. This is a conditional illustration of how the bridge
could be warranted, not a proof about every concrete effect or evidence that
set ontology is obligatory. It also does not prove that the singleton's
ordinary counterfactual relation has the exact frozen q.44 interpretation.

The needed distinction is between an identity-preserving possibility in which
x survives without **this y**, and a different individual or a different kind
of source satisfying a generic description. “Every received act has some
source” alone leaves substitution possible. Historical origin dependence also
does not immediately settle present coexistence with the originator.

### Draft sufficient package P1-A

Fix one reference situation, one domain of bearers, one interpretation of
cross-situation identity, one time/aspect convention, and one admitted
possibility predicate `A v`. Let `Exists v x` mean existence in that same
comparison, and let `Dv v x y` be a world-indexed extension of the intended
counterfactual dependence. The draft obligations are:

```text
Possibility witness:
  ∀ x y, W x y → ∃ v, A v ∧ Exists v x ∧ ¬ Exists v y

Persistence of the dependency when its bearer exists:
  ∀ x y, D x y → ∀ v, A v → Exists v x → Dv v x y

Centering at an admitted situation where the source is absent:
  ∀ v x y, A v → ¬ Exists v y → Dv v x y → ¬ Exists v x
```

The proof plan is short: a witness to `W x y` supplies an admitted v with x
and without y; persistence supplies `Dv v x y`; centering supplies nonexistence
of x there. These conflict. Only the displayed direction of the possibility
representation is needed. Agreement of `Dv` with the frozen D in the reference
situation is part of interpreting it as an extension, even though that
agreement is not an additional logical step in this proof sketch.

The main substantive input is persistence. Its best candidate warrant is an
independently supported **essential existential requirement on this source**,
plus the claim that admitted possibilities preserve that essence. If
persistence is introduced merely because P1 is desired, this package explains
the logical gap but does not supply new warrant. Centering is also an explicit
rule of the chosen counterfactual semantics, not a property already registered
for the primitive D.

A nearest-situation counterfactual may hold at the reference situation even
though a more remote, identity-preserving possibility has a replacement
source. That is a concrete reason to distinguish the two questions. It is not
by itself evidence that such a replacement exists for the metaphysical source
at issue. A freely assigned finite model would only diagnose non-entailment.

For necessarily existing sources, absence has no ordinary possible witness.
The modal exclusion may then be immediate, while the q.44 dependence question
still asks for a meaningful nonvacuous counterpossible account. P1-A does not
construct that account or infer productive dependence from the absence of
possible absence worlds.

### Assessment and next test

The strongest positive route is essential source dependence, with direct
prima facie acceptance available in a clearly stated local domain. The exact
universal P1 remains unresolved because the frozen D does not already certify
that every one of its links persists across all admitted possibilities.

The next discriminating test is to take a defended instance of D and specify
its identity conditions and source role before evaluating absence. Does the
same bearer admit a different source while retaining those conditions? If
not, give the independent essentiality argument; if so, determine whether the
original D was contextual or historical. Neither conclusion should be selected
by changing the comparison domain after seeing the answer.

## 5. P2: a new connection to strict grounding without well-foundedness

### Positive rationale and exact reusable theorem

An explanation in which y supplies the very existential actuality derived by
x is naturally directed: using x's receipt of that actuality to account for
y's supplying it threatens to leave the receipt unaccounted for. This gives
prima facie motivation for strict existential explanation. To turn that
motivation into P2, the work is to justify that D expresses this kind of
derivation, not merely co-presence, reciprocal constraints, or explanatory
equivalence. Numerical distinctness alone does not perform that work.

The existing PLG result offers a precise conditional consequence. In the
repository vocabulary:

```text
StrictlyGrounds S A B := Derivable S (strictPartial A B)
Consistent S := ∃ s, ¬ Derivable S s

For every Atom and S, if Consistent S, then:
  ∀ A B, StrictlyGrounds S A B →
    ¬ Derivable S (weakPartial B A)
```

This is the second conjunct of statement
`307261a0-1fcf-5920-a3cd-ebfe29a7617e`, proved by the existing result above.
Its Solution combines `Derivable.transStrictWeak` with noncircularity and
consistency. `Derivable.subsumptionStrictPartial` converts a reverse strict
edge into the prohibited reverse weak edge. This identifies actual reusable
inference machinery, rather than appealing generally to “grounding theory.”

### Draft sufficient package P2-A

Choose atoms that faithfully represent existence facts for the same beings in
one fixed situation, with mapping `e : B → Atom`. Require:

```text
Consistency:
  Consistent S

Dependence-to-strict-ground interpretation:
  ∀ x y, x ≠ y → D x y → StrictlyGrounds S (e y) (e x)
```

Given distinct x and y with both dependence directions, the interpretation
supplies two opposite strict edges. Subsumption makes the second a weak
reversal of the first; the existing nonreversal theorem excludes it. This is
a proposed composition, not a newly executed Lean proof. It needs neither a
finite universe nor well-foundedness, a first cause, or a general sufficient
reason principle.

The mapping is oriented cause/source fact first, dependent existence fact
second. Injectivity of `e` is not needed by the displayed syntactic argument,
but honest individuation, actuality, and the interpretation of the atoms are
still essential to applying it to the intended beings. If one can justify the
mapping only for actual concreta or a selected class of essential dependencies,
the result is that restricted P2. A further coverage premise is needed for the
frozen unqualified quantifier.

### What the package gains, and what it does not

The PLG theorem is independently reusable and currently has no root-path
consumer. It avoids deriving P2 through efficient-cause priority results that
already consume P2. It also separates noncircularity from the stronger issue of
infinite regress.

The substantial new bridge remains open. In the intended strict-partial sense,
nonreversibility belongs to the interpretation of strictness. An argument that
simply labels every D link “strict” has moved the disputed content into the
dictionary. To improve warrant, the dictionary needs an independent account
of why existence is supplied/constituted on one side and received on the other.
Consistency of the selected S also needs warrant; the universally quantified
PLG theorem cannot establish that S.

The genuine scope alternative is weak explanatory dependence or reciprocal
constraints. Fine's weak/strict distinction provides positive vocabulary for
that alternative, but examples of equivalent truths are not automatically
examples of distinct beings mutually dependent for esse. The present reading
therefore does not record a metaphysical refutation of P2. It identifies what
a proposed counterinstance would have to preserve: distinct bearers, the same
existential respect and situation, both links in the **frozen** D sense, and
grounds for treating them as more than an arbitrary relation assignment.

Ordinary feedback across successive times or different respects is likewise
not a reciprocal same-respect existential derivation. It can challenge a
careless unqualified causal slogan without settling the typed premise.

### Assessment and next test

P2 has a strong conditional route under strict explanatory dependence. The
existing source support motivates that direction for already ordered
prior/posterior pairs; it does not independently quantify over all D pairs.
The key next task is an existence-fact bridge for a substantive dependency
instance, together with an independently motivated consistent theory of its
grounds. A successful local bridge should be tested for extension of scope
before registering the global premise. No termination assumption is needed.

## 6. P8: received esse, same-respect effects, and export to the bearer

### Positive conservation argument, with its premises exposed

The strongest candidate is a received-act argument, already developed in the
earlier note. It can be expressed without building the desired dependence into
the name of a causal relation:

1. The present esse of this very bearer is received and currently derivative,
   rather than merely having been received at its origin.
2. Such a current derivative actuality requires a concurrent productive
   actualization; a historical production plus a persistence law does not
   exhaust its explanation.
3. The identified agent's relevant contribution supplies that esse and is
   indispensable in the counterfactual comparison, with the same bearer,
   time/aspect, causal role, and background conditions retained.
4. Withdrawal of that contribution is appropriately represented by the frozen
   dependence counterfactual, including an explicit account when source absence
   is impossible.

These are proposed metaphysical and semantic premises, not new attributions to
a source. They make clear why the conservation interpretation can support
existential dependence: present being is received through an indispensable
present act. They also make clear why origin-receipt, essence/esse nonidentity,
or a field named `givingEsse` alone is insufficient. Premises 2–4 still need
defense for the selected case.

The global divine-conservation conclusion in q.104 already presupposes God.
Importing that conclusion into a proof of God's existence would beg the
question. What is reusable here is the general analysis of becoming, being,
and continuing source contribution, conditional on an independently supported
instance. Neither the source nor this package supplies a new God-existence
premise without those independent grounds.

The existing narrower sibling is already available:

```text
2068f91c-1eeb-5dbb-a71a-f7b6a12bb495
EsseEffectDependsOnItsCause:
  ∀ c x, c ≠ x → CausesIn c x esse → D x c
```

It is an open analyst premise, not a closed result. Its four-premise route to
actual concrete grounding is listed in section 3. It supplies a useful
destination for a well-supported received-esse account without requiring all
efficient causality to have the same scope.

### Draft sufficient package P8-A for the unchanged target

To derive the frozen all-r P8 from that sibling, one sufficient package is:

```text
EsseEffectDependsOnItsCause CausesIn esse D

NothingIsEfficientCauseOfItselfReading E
  (∀ x r, ¬ E x x r)

Same-bearer esse export:
  ∀ c x r, E c x r → CausesIn c x esse
```

For an E edge, the second premise gives distinctness; the third supplies an
esse-causing edge with the SAME c and x; the first supplies D. This specifies
the missing universal transfer. The no-self premise must be justified by a
route that does not already rely on the P8 being derived; using
`CausalMapsBatch1.nothingEfficientCauseOfItself` for it would be circular here.

The export is not present in the definition of E and is not supplied by the
source scope reviewed. Even a universal conserver of all bearers would not
show that every distinct agent producing an accidental determination is that
bearer's conserver. Replacing x with the temperature, illumination, or event
that c produces changes the endpoint and does not establish P8 for x.

A same-respect alternative would introduce dependence of **x's being r** on c,
then prove a separate transfer to the existence of x when r is esse or
independently shown essential to x. That is a new typed sibling/bridge project,
not a reinterpretation of the current target. When reusing the existing
esse-specific sibling, the separate `EfficientlyCausesIn` to `CausesIn`
dictionary must also be explicit.

### Evidence, alternatives, and limits of illustrations

The builder/house and retained-heat examples support the need to distinguish
causal roles; they do not discriminate a conserver's absence because they
remove a producing activity of a different kind. Likewise, the historical
illumination analogy should not be promoted to a present-day physical
measurement of instantaneous dependence. A controlled interruption could
provide evidence for a particular maintained process; identifying that process
with the esse of its bearer needs a further argument.

The serious alternative examined in the earlier note is historical production
plus a stable persistence law: a presently actual bearer persists unless an
independently specified destructive condition occurs. To carry an existential
conclusion, the law must explain why every existential loss is covered by those
conditions. “No change” cannot simply abbreviate survival, and mere qualitative
constancy is not that coverage. Conversely, rejecting this alternative requires
an argument that only concurrent efficient actualization explains received
esse. Neither side is established merely by restating its adequacy requirement.

An intrinsic power that produces its own bearer's existence may raise the
priority circularity treated by the existing self-actualization results. That
does not automatically exclude an extrinsic historical or law-based account,
nor does it exclude a being maintaining some already present determination.
The same identity, respect, and time must survive the comparison.

### Assessment and next test

The received-esse route retains substantive positive warrant; the exact
strengthening to every respect remains poorly supported by the sources and
interfaces inspected. This is a reason to pursue the narrower route in
parallel, not to delete the old premise or declare a metaphysical falsity from
a mathematical omission model.

The next discriminating investigation needs an independently described
productive contribution to the existence of one and the same bearer, followed
by a reasoned comparison with the historical-law account. A new Boolean loss
flag, a predicate named “adequate explanation,” or a repeated appeal to origin
does not resolve the remaining issue. For the unchanged P8, an additional
same-bearer argument covering every causal respect would still be required.

## 7. Joint constraints, outcome, and reopening conditions

These three premises should not be assessed under shifting senses of D. If P1
is combined with the separate independence-allows-being-without premise and
classical contraposition, the resulting draft equivalence is `D x y ↔ ¬ W x y`.
Under a full modal interpretation of W, P2 then rules out reciprocal necessary
coexistence of distinct beings. This is a conditional interaction to inspect,
not an observed metaphysical counterexample or a newly verified corpus result.
Necessary backgrounds and essential coexistence must be handled explicitly
before a global modal collapse is adopted.

The most useful new connection is **P2-A**: the existing PLG nonreversal result
can be composed with a separately defended dependence-to-strict-ground bridge.
Its exact open obligations are consistency of the selected sequent theory,
faithful existence-fact interpretation, and coverage of the frozen D domain.
The most direct source-supported causal continuation is the existing
esse-specific sibling; its received-act rationale and historical-law rival
remain explicit. P1-A gives a concrete way to identify and investigate the
essentiality premise needed by a modal continuation.

No root premise is discharged and no support edge is registered by this note.
The work preserves both direct acceptance and conditional derived options.
Reopening is warranted by a materially better essential-source argument, an
actual dependence/strict-ground interpretation with a consistent theory, a
productive account of the same bearer's present esse, or an independent
existential persistence/destruction-coverage argument. Further diagrams or
arbitrary relation assignments alone would not settle these questions.

## 8. Validation boundary

The current work adds this research note and three attempt records only.
`truth check` passed, reporting 545 attempts and the existing corpus warnings.
`source_evidence.py check` passed for 512 passages and 2,048 formalized claims;
its one bibliographic and one permanently unavailable witness remain explicitly
not byte-verified. `docs_index.py`, staged `git diff --check`, and
`attribution-check --base 03d97b48a86d4b7d7bbedcb4441398ce3a9dadef` passed;
the attribution check found no new or changed stating claim.

Computed `frontier-diff` against that baseline reports `changed: false` for
both the default Catholicism root and `STMT-GOD-EXISTS`, with no added/removed
support bundles or route changes. The God target retains 314 support bundles
and 396 open premises (276 bare, 40 stated, 80 supported). These are ordinary
CLI frontier counts, not a new recomputation of the terminal BDD family.

The configured verifier toolchain is unavailable in this worker environment.
No fresh Lean, Comparator, or NanoDa success is claimed; unchanged registered
formal results are reused as existing evidence.
