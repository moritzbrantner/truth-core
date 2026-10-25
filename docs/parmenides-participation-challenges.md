# Whole/part participation, explanatory distance and knowledge

Issue #259 tests three objections without identifying numerical difference,
independent existence, non-inherence and cognitive isolation. The interface in
`TruthCore/Greek/Plato/Parmenides/ParticipationChallenges.lean` extends the shared
`Forms.Vocabulary`; it changes none of its meanings or existing theories.

## Source reading and boundaries

The primary Greek witnesses were materialized before interpretation: Parmenides
130, 131, 133 and 134; Aristotle Metaphysics I.9; Phaedo 74 and 100; Timaeus 28
and 29. Full pages/chapters supply the surrounding exchange. The 131/133/I.9
manifests are shared identically with #258, whose regress readings concern a
different part of the text. No translation or search snippet supplies a claim.

At 130e–131a participation is challenged as whole-or-part reception. At 131b
Socrates answers with the one day in many places; Parmenides substitutes the
sail distributed over many people. The typed spatial dilemma isolates that
substitution. `WholeExclusive` is **open**: distinct bearers cannot receive the
same spatial whole. It includes an individuation/localization condition stronger
than merely different objects or numerical unity; the proof does not silently
infer that distinct objects occupy disjoint places. `IndivisibleForms` separately
records the exchange's refusal to divide the one Form. No modern measure theory
is attributed to Plato. The further largeness/equality/smallness difficulties at
131c–e are recorded as their own reading, with their comparative-property
semantics still open; the generic proof uses indivisibility instead.

At 133b–134e Parmenides presses the greatest difficulty using relations among
Forms and among things with us. The reconstruction projects the knowledge/object
relation into agent-indexed cognitive modes; it does not identify an agent with a
Form of Knowledge. `HumanOutside`, `DivineInside`, and `KnowledgeRealmClosure`
are separately named assumptions. The divine horn is conditional on the divine
mode using knowledge-itself, not a conclusion that no god could know particulars
in any mode. No premise asserts omniscience or divine existence.

Aristotle's 991a8–19 criticism asks what separate Forms contribute to knowledge,
being or change. The reconstruction keeps his non-inherence setting distinct
from the modern **open** universal `GroundRequiresInherence`. That universal is
not attributed to Aristotle. `ExplanationGrounds` is likewise an open bridge
from the existing quality-indexed explanation to directed dependence.

The charitable replies have distinct source readings. Phaedo 100d–e leaves the
manner of explanatory presence/communion unspecified; it does not establish a
modern theory of ground. Timaeus 28a–b distinguishes the stable model from the
craftsman's productive role. `ModelMakerBridge` records a universal maker
existence/sufficiency proposal as **open**, including its additional numerical
distinctness premise; the finite grounding model does not satisfy this bridge.
Phaedo 74b–d proposes access to the Equal itself through equal sensible objects;
its recollective setting presupposes relevant prior knowledge, so it is not an
empiricist derivation or a universal inference from resemblance. The proposed
`MediatedTransfer` warrant and successful `HumanRoute` remain independent open
premises. These cross-dialogue replies are not presented as solutions uttered
in Parmenides or as Plato's final doctrine.

## Mechanically advertised arguments

Each row names a separate frozen Challenge, Solution, argument and Comparator
result. The theorem is in
`TruthCore.Results.Greek.Plato.Parmenides.<folder>.<theorem>`.

| Result | Folder / theorem | Premises and consequence |
| --- | --- | --- |
| `PARM-WHOLE-PART-OBJECTION` | `WholePartObjection.wholePartObjection` | Two distinct F particulars; one common Form; whole exclusion; Form indivisibility. Part allocation contradicts indivisibility, while two whole allocations contradict exclusion. Therefore the spatial dilemma fails. |
| `PARM-NONSPATIAL-REPLY` | `NonspatialReply.nonspatialReply` | Premise-free construction importing `PLATONIC-SELF-PREDICATING-CONSISTENT` and the previous theorem. Keep two particulars, a unique common independent explanatory Form and nonidentity; interpret spatial whole/part allocation as empty. Participation survives without spatial distribution. |
| `PARM-DISTANCE-OBJECTION` | `DistanceObjection.distanceObjection` | An F particular; explanatory participation; non-inherent Forms; explanation-to-ground bridge. An explanatory Ground edge cannot satisfy a universal inherence requirement. The result identifies incompatible commitments without choosing which to abandon. |
| `PARM-RANKED-ASYMMETRY` | `RankedAsymmetry.rankedAsymmetry` | Every Ground edge increases a natural-number rank. A reverse edge would yield a strict-order cycle; therefore Ground is asymmetric. Rank is neither time nor a degree of reality. |
| `PARM-GROUND-REPLY` | `GroundReply.groundReply` | Premise-free finite construction with an actual Form/particular explanatory pair, independence, nonidentity, non-inherence and ranked asymmetric Ground. It imports the asymmetry theorem. Efficient change-production is empty. |
| `PARM-EPISTEMIC-OBJECTION` | `EpistemicObjection.epistemicObjection` | Knowledge realm closure, human modes outside and divine modes inside. Humans cannot know intelligible objects; divine modes cannot know non-intelligible objects. Both horns follow from the explicit closure premise. |
| `PARM-MEDIATION-REPLY` | `MediationReply.mediationReply` | Human modes outside, sound mediated transfer, and a successful human route to an intelligible object. The resulting knowledge contradicts realm closure. It does not contradict independent existence. |
| `PARM-MEDIATION-MODEL` | `MediationModel.mediationModel` | Premise-free construction with separate entity and agent argument roles, both represented by Bool, and human and divine modes, and opposite-side presentations. Prove transfer by substituting the directly accessed presentation, then compose MediationReply. A divine mode also knows a non-intelligible object. |

The generic cognition interface has separate entity and agent type parameters;
the finite witness uses Bool for both representation domains. Equal Boolean
labels across those roles are not an asserted philosophical identification of
an agent with a Form. The finite witnesses interpret relations with explicit extensions. They establish
compatibility of the encoded conditions, not that any such extension describes
real explanation or warranted knowledge. In particular the knowledge model does
not infer truth from resemblance: presentation nonidentity and direct-access
identity compose to its explicitly interpreted object-directed knowledge edge.
Neither model supplies an independent epistemology or a causal mechanism.

## What stays unresolved

The ordinary frontier exposes `STMT-PARM-WHOLE-EXCLUSIVE`,
`STMT-PARM-INDIVISIBLE-FORMS`, `STMT-PARM-NONINHERENT-FORMS`,
`STMT-PARM-EXPLANATION-GROUNDS`, `STMT-PARM-RANKED-GROUND`,
`STMT-PARM-KNOWLEDGE-REALM-CLOSURE`, `STMT-PARM-HUMAN-OUTSIDE`,
`STMT-PARM-DIVINE-INSIDE`, `STMT-PARM-MEDIATED-TRANSFER` and
`STMT-PARM-HUMAN-ROUTE` as premises where they are used. The disputed spatial
dilemma and universal inherence requirement are conclusions' negated targets,
not silently established premises. `STMT-PARM-MODEL-MAKER-BRIDGE` records an
additional open causal proposal, with source support but no proof. Three
candidates preserve the spatial reading, explanatory adequacy and epistemic
warrant obligations. None of these results closes a Catholic-case root path or
advertises a blanket refutation of Forms.

## Fidelity and proof self-sweep

The whole/part conclusion is accepted as a consequence of its explicit spatial
and indivisibility assumptions; the nonspatial reply genuinely keeps the earlier
Forms commitments rather than restating a proved conclusion as a premise.
The distance conclusion is accepted as the incompatibility of inherence and
non-inherent Ground edges; adequacy of such edges is not proved. The rank lemma
is strict-order reasoning. The epistemic horns and mediation incompatibility are
accepted under their exact modes and transfer premises. The finite models show
only existence of interpretations, and may fail under stronger philosophical
requirements.

Every new statement and source reading links the relevant existing Forms senses
and the new spatial, grounding or knowledge senses. The four new disambiguations
cover spatial sharing, static explanation versus change-production,
non-inherence versus cognitive isolation, and presentation versus known object.
All attributed readings have been checked against the verified complete source
context; modern universal bridges, localization, rank and mediation sufficiency
are explicitly unattributed. Source integrity, source fidelity and formal
consequence remain separate claims.

Convention resolution used source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.
