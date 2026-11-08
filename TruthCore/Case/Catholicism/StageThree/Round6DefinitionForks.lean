module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
public import TruthCore.Case.Catholicism.StageThree.CommissionDefinitions
public import TruthCore.Case.Catholicism.StageThree.FoundingDefinitions
public import TruthCore.Case.Catholicism.StageThree.CommissionAttestation

/-!
# Round 6: stage-3 definition forks (Church criterion, governing criterion, founding reading)

Open analyst premises for derivations of ten stage-3 root-path statements that
the derivation worklist (`corpus.py thickness --queue`) lists without a verified
non-transcription derivation. Each target is one side of an existing
definition fork: a definition proposition (the selected predicate coextends
with a named criterion), its negation, or the named coverage of a fork.

* map `explorations/round6-church-criteria.toml`: `JointAspectCriterion`,
  `VisibleCriterion`, `SpiritualCriterionFails` and `NamedChurchCoverage` from
  inclusion conditions between the selected Church predicate, the visible
  authoritative predicate and the spiritual-community predicate;
* map `explorations/round6-governance-criteria.toml`:
  `NarrowGovernanceCriterionFails`, `TeachingInclusiveGovernanceCriterion`,
  `NamedGovernanceCoverage` and `InstitutionLinkFor` from inclusion conditions
  between the selected governing predicate and the fixed nine-power table;
* map `explorations/round6-founding-attestation.toml`: `ImmediateReadingFails`
  from a God-founded Jesus-envoy teaching event and the existing direct/envoy
  exclusion, and `JohnCommissionIndependent` from the fixed strand table.

Every definition below is an OPEN analyst formulation with attribution
deferred. Each is a half of a definition proposition (one inclusion), a
cross-predicate inclusion, or a witness; none states a target. The derivations
in `TruthCore.Results.Case.Catholicism.StageThree.Round6DefinitionForks`
compose them, and the omission controls there show which premise each
derivation needs. The predicates `church`, `spiritual`, `governing` and
`direct` remain the parameters of the existing definition modules; their
domain is the fixed Society/profile scope of those modules, not a census of
real societies, powers or ecclesiologies.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation

/-! ## Map 1: Church criteria -/

/-- OPEN analyst premise: every society satisfying the selected Church
predicate is a visible society with an authority structure (one direction of
`VisibleCriterion`; it does not say that every such society is the Church).
A purely invisible church of the elect falsifies it. -/
def SelectedChurchIsVisible (σ : Signature) (church : σ.Society → Prop) : Prop :=
  ∀ c, church c → σ.VisibleWithAuthority c

/-- OPEN analyst premise: every society satisfying the selected Church
predicate is a spiritual community (one direction of `SpiritualCriterion`).
A merely juridical church without inward communion falsifies it. -/
def SelectedChurchIsSpiritual (σ : Signature) (church spiritual : σ.Society → Prop) : Prop :=
  ∀ c, church c → spiritual c

/-- OPEN analyst premise: a society that is both visible with authority and a
spiritual community is the selected Church (the converse direction of
`JointAspectCriterion`). Two rival visible bodies with spiritual communion
falsify it, unless the profile counts both under the Church predicate. -/
def VisibleSpiritualSocietyIsChurch (σ : Signature) (church spiritual : σ.Society → Prop) :
    Prop :=
  ∀ c, σ.VisibleWithAuthority c → spiritual c → church c

/-- OPEN and contested analyst premise, at the fixed profile scope: every
visible society with authority in the scope is a spiritual community. It does
not say that every spiritual community is visible. A visible authoritative
society without spiritual communion in the scope falsifies it. -/
def VisibleSocietyIsSpiritual (σ : Signature) (spiritual : σ.Society → Prop) : Prop :=
  ∀ c, σ.VisibleWithAuthority c → spiritual c

/-- OPEN analyst witness premise: some spiritual community in the scope is not
a visible society with authority (for instance a communion of grace that lacks
the visible hierarchical constitution). It does not say that this community is
not the Church; that follows only with `SelectedChurchIsVisible`. -/
def SomeSpiritualCommunityNotVisible (σ : Signature) (spiritual : σ.Society → Prop) : Prop :=
  ∃ c, spiritual c ∧ ¬ σ.VisibleWithAuthority c

/-! ## Map 2: governing criteria -/

/-- OPEN analyst premise: the selected governing predicate includes the power to
teach. It says nothing about the other eight powers. -/
def SelectedGoverningIncludesTeaching (governing : Power → Prop) : Prop :=
  governing .teach

/-- OPEN analyst premise: every power the fixed table classifies as governing
(keys, binding and loosing, judging, forgiving and retaining, shepherding)
satisfies the selected governing predicate. -/
def TableGoverningIsSelected (governing : Power → Prop) : Prop :=
  ∀ p, p.Governing = true → governing p

/-- OPEN analyst premise: every selected governing power is classified as
governing by the fixed table or is the power to teach. A criterion that also
counts baptizing or preaching as governing falsifies it. -/
def SelectedGoverningWithinTableOrTeaching (governing : Power → Prop) : Prop :=
  ∀ p, governing p → p.Governing = true ∨ p = .teach

/-- OPEN analyst bridge: for any `g`, if Jesus holds a mandate from `g` and
founded the Catholic Church as a visible society with authority, then his
giving (or promising) the power to teach founds that Church in the exercise of
that mandate. It is the teaching instance of the first clause of the
institutional link; the message rival, which reads teaching as conveying content
only, denies it. -/
def TeachingGrantFoundsInMandate (σ : Signature) (A : Agency σ) (E : Commissioning) : Prop :=
  ∀ g, A.HoldsMandate σ.jesus g →
    σ.Founded σ.jesus σ.catholicChurch → σ.VisibleWithAuthority σ.catholicChurch →
      E.Gave .teach → A.FoundedInMandate σ.jesus g σ.catholicChurch

/-! ## Map 3: founding reading and attestation -/

/-- OPEN analyst witness premise: some God candidate founded as a teaching
authority a society that Jesus founded in the mandate relation to that God and
commissioned to teach. It does not say that every such event is a founding by
God (that is the existing envoy bridge `EnvoyFoundingIsPrincipalsFounding`),
and it does not say whether the founding was direct. -/
def GodFoundedSomeJesusEnvoySociety (σ : Signature) (A : Agency σ) : Prop :=
  ∃ g c, σ.IsGod g ∧ EnvoyTeachingEvent σ A g c ∧ σ.FoundedAsTeachingAuthority g c

/-- OPEN analyst premise about the literary relations of the commission
reports: every Johannine commission saying is independent of every Matthean
one (`Tradition.Independent`). The strand of each report is the fixed table
`strandOf`. Whoever holds that John knew and used Matthew denies it. -/
def JohannineSayingsIndependentOfMatthean (T : Tradition) : Prop :=
  ∀ r₁ r₂, strandOf r₁ = .johannine → strandOf r₂ = .matthean → T.Independent r₁ r₂

/-! ## Controls: finite interpretations

Omission models and one nonvacuity witness per map. Society carrier `Three`
for the Church map, `Unit` elsewhere; beings are `Bool` (`true` is the God
candidate, `false` is Jesus). These are schema interpretations only. -/

namespace Control

open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions

/-- A three-society carrier for the Church map. -/
inductive Three
  | a | b | c
  deriving DecidableEq, Repr

/-- A subset of `Three`, given by membership of `a`, `b`, `c`. -/
def tri (x y z : Bool) : Three → Bool
  | .a => x
  | .b => y
  | .c => z

/-- The predicate of the subset `tri x y z`. -/
abbrev P (x y z : Bool) (s : Three) : Prop := tri x y z s = true

/-- A model signature on society carrier `S` with visible predicate `V` and
founding-as-teaching-authority relation `fta`. -/
abbrev sig (S : Type) (c0 : S) (V : S → Prop) (fta : Bool → S → Prop) : Signature where
  Being := Bool
  IsGod b := b = true
  HasClassicalAttributes _ := True
  RevealsRecognizably _ := True
  jesus := false
  ClaimedDivineAuthority _ := True
  RoseFromTheDead _ := True
  Society := S
  catholicChurch := c0
  Founded _ _ := True
  VisibleWithAuthority := V
  FoundedAsTeachingAuthority := fta
  DefinitivelyProposesAsRevealed _ _ := True
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

/-- Church-map signature: visible societies `tri vx vy vz`. -/
abbrev churchSig (vx vy vz : Bool) : Signature :=
  sig Three .a (P vx vy vz) (fun _ _ => True)

/-- One-society signature with constant founding-as-teaching-authority `fta`. -/
abbrev unitSig (fta : Prop) : Signature :=
  sig Unit () (fun _ => True) (fun _ _ => fta)

/-- Agency on `unitSig` with constant mandate, in-mandate founding and
teaching commission. -/
abbrev unitAgency (fta mandate inMandate teach : Prop) : Agency (unitSig fta) where
  Confirms _ _ := True
  HoldsMandate _ _ := mandate
  FoundedInMandate _ _ _ := inMandate
  CommissionedToTeach _ _ := teach

/-! ### Map 1: Church criteria -/

/-- `churchJointFromAspects`, omit `SelectedChurchIsVisible`: church = spiritual
= {a}, nothing visible. -/
def omitVisibleJoint : Prop :=
  ¬ SelectedChurchIsVisible (churchSig false false false) (P true false false) ∧
    SelectedChurchIsSpiritual (churchSig false false false) (P true false false) (P true false false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig false false false) (P true false false) (P true false false) ∧
    ¬ JointAspectCriterion (churchSig false false false) (P true false false) (P true false false)

/-- `churchJointFromAspects`, omit `SelectedChurchIsSpiritual`: church = visible
= {a}, nothing spiritual. -/
def omitSpiritualJoint : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P true false false) ∧
    ¬ SelectedChurchIsSpiritual (churchSig true false false) (P true false false) (P false false false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig true false false) (P true false false) (P false false false) ∧
    ¬ JointAspectCriterion (churchSig true false false) (P true false false) (P false false false)

/-- `churchJointFromAspects`, omit `VisibleSpiritualSocietyIsChurch`: no church,
visible = spiritual = {a}. -/
def omitBothJoint : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P false false false) ∧
    SelectedChurchIsSpiritual (churchSig true false false) (P false false false) (P true false false) ∧
    ¬ VisibleSpiritualSocietyIsChurch (churchSig true false false) (P false false false) (P true false false) ∧
    ¬ JointAspectCriterion (churchSig true false false) (P false false false) (P true false false)

/-- `churchVisibleFromAspects`, omit `SelectedChurchIsVisible`. -/
def omitVisibleVisible : Prop :=
  ¬ SelectedChurchIsVisible (churchSig false false false) (P true false false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig false false false) (P true false false) (P false false false) ∧
    VisibleSocietyIsSpiritual (churchSig false false false) (P false false false) ∧
    ¬ VisibleCriterion (churchSig false false false) (P true false false)

/-- `churchVisibleFromAspects`, omit `VisibleSpiritualSocietyIsChurch`. -/
def omitBothVisible : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P false false false) ∧
    ¬ VisibleSpiritualSocietyIsChurch (churchSig true false false) (P false false false) (P true false false) ∧
    VisibleSocietyIsSpiritual (churchSig true false false) (P true false false) ∧
    ¬ VisibleCriterion (churchSig true false false) (P false false false)

/-- `churchVisibleFromAspects`, omit `VisibleSocietyIsSpiritual`. -/
def omitVisSpiritualVisible : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P false false false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig true false false) (P false false false) (P false false false) ∧
    ¬ VisibleSocietyIsSpiritual (churchSig true false false) (P false false false) ∧
    ¬ VisibleCriterion (churchSig true false false) (P false false false)

/-- `spiritualFailsFromInvisibleCommunion`, omit `SelectedChurchIsVisible`:
church = spiritual = {a}, nothing visible. -/
def omitVisibleFails : Prop :=
  ¬ SelectedChurchIsVisible (churchSig false false false) (P true false false) ∧
    SomeSpiritualCommunityNotVisible (churchSig false false false) (P true false false) ∧
    ¬ SpiritualCriterionFails (churchSig false false false) (P true false false) (P true false false)

/-- `spiritualFailsFromInvisibleCommunion`, omit the invisible-communion witness:
church = spiritual = visible = {a}. -/
def omitInvisibleFails : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P true false false) ∧
    ¬ SomeSpiritualCommunityNotVisible (churchSig true false false) (P true false false) ∧
    ¬ SpiritualCriterionFails (churchSig true false false) (P true false false) (P true false false)

/-- `namedChurchCoverageFromAspects`, omit `SelectedChurchIsVisible`: visible
{a}, spiritual {a,b,c}, church {a,b}. -/
def omitVisibleCoverage : Prop :=
  ¬ SelectedChurchIsVisible (churchSig true false false) (P true true false) ∧
    SelectedChurchIsSpiritual (churchSig true false false) (P true true false) (P true true true) ∧
    VisibleSpiritualSocietyIsChurch (churchSig true false false) (P true true false) (P true true true) ∧
    ¬ NamedChurchCoverage (churchSig true false false) (P true true false) (P true true true)

/-- `namedChurchCoverageFromAspects`, omit `SelectedChurchIsSpiritual`: visible
{a,b,c}, spiritual {a}, church {a,b}. -/
def omitSpiritualCoverage : Prop :=
  SelectedChurchIsVisible (churchSig true true true) (P true true false) ∧
    ¬ SelectedChurchIsSpiritual (churchSig true true true) (P true true false) (P true false false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig true true true) (P true true false) (P true false false) ∧
    ¬ NamedChurchCoverage (churchSig true true true) (P true true false) (P true false false)

/-- `namedChurchCoverageFromAspects`, omit `VisibleSpiritualSocietyIsChurch`:
no church, visible = spiritual = {a}. -/
def omitBothCoverage : Prop :=
  SelectedChurchIsVisible (churchSig true false false) (P false false false) ∧
    SelectedChurchIsSpiritual (churchSig true false false) (P false false false) (P true false false) ∧
    ¬ VisibleSpiritualSocietyIsChurch (churchSig true false false) (P false false false) (P true false false) ∧
    ¬ NamedChurchCoverage (churchSig true false false) (P false false false) (P true false false)

/-- Map 1 witness: visible {a}, spiritual {a,b}, church {a}. Every premise and
conclusion holds, with a selected Church and an invisible spiritual community. -/
def witnessChurch : Prop :=
  (∃ s, P true false false s) ∧
    SelectedChurchIsVisible (churchSig true false false) (P true false false) ∧
    SelectedChurchIsSpiritual (churchSig true false false) (P true false false) (P true true false) ∧
    VisibleSpiritualSocietyIsChurch (churchSig true false false) (P true false false) (P true true false) ∧
    VisibleSocietyIsSpiritual (churchSig true false false) (P true true false) ∧
    SomeSpiritualCommunityNotVisible (churchSig true false false) (P true true false) ∧
    JointAspectCriterion (churchSig true false false) (P true false false) (P true true false) ∧
    VisibleCriterion (churchSig true false false) (P true false false) ∧
    SpiritualCriterionFails (churchSig true false false) (P true false false) (P true true false) ∧
    NamedChurchCoverage (churchSig true false false) (P true false false) (P true true false)

/-! ### Map 2: governing criteria -/

/-- The fixed table as a selected governing predicate. -/
abbrev tableGov (p : Power) : Prop := p.Governing = true

/-- Teaching only. -/
abbrev teachGov (p : Power) : Prop := p = .teach

/-- The teaching-inclusive predicate. -/
abbrev inclusiveGov (p : Power) : Prop := p.Governing = true ∨ p = .teach

/-- `narrowFailsFromTeaching`, omit `SelectedGoverningIncludesTeaching`. -/
def omitTeachNarrow : Prop :=
  ¬ SelectedGoverningIncludesTeaching tableGov ∧ ¬ NarrowGovernanceCriterionFails tableGov

/-- `teachingInclusiveFromBounds`, omit `SelectedGoverningIncludesTeaching`. -/
def omitTeachInclusive : Prop :=
  ¬ SelectedGoverningIncludesTeaching tableGov ∧ TableGoverningIsSelected tableGov ∧
    SelectedGoverningWithinTableOrTeaching tableGov ∧
    ¬ TeachingInclusiveGovernanceCriterion tableGov

/-- `teachingInclusiveFromBounds`, omit `TableGoverningIsSelected`. -/
def omitTableInclusive : Prop :=
  SelectedGoverningIncludesTeaching teachGov ∧ ¬ TableGoverningIsSelected teachGov ∧
    SelectedGoverningWithinTableOrTeaching teachGov ∧
    ¬ TeachingInclusiveGovernanceCriterion teachGov

/-- `teachingInclusiveFromBounds`, omit `SelectedGoverningWithinTableOrTeaching`:
every power governing. -/
def omitWithinInclusive : Prop :=
  SelectedGoverningIncludesTeaching (fun _ => True) ∧ TableGoverningIsSelected (fun _ => True) ∧
    ¬ SelectedGoverningWithinTableOrTeaching (fun _ => True) ∧
    ¬ TeachingInclusiveGovernanceCriterion (fun _ => True)

/-- `namedGovernanceCoverageFromBounds`, omit `TableGoverningIsSelected`: no
power governing. Excluded middle is a logical principle and is not varied. -/
def omitTableCoverage : Prop :=
  ¬ TableGoverningIsSelected (fun _ => False) ∧
    SelectedGoverningWithinTableOrTeaching (fun _ => False) ∧
    ¬ NamedGovernanceCoverage (fun _ => False)

/-- `namedGovernanceCoverageFromBounds`, omit
`SelectedGoverningWithinTableOrTeaching`: every power governing. -/
def omitWithinCoverage : Prop :=
  TableGoverningIsSelected (fun _ => True) ∧
    ¬ SelectedGoverningWithinTableOrTeaching (fun _ => True) ∧
    ¬ NamedGovernanceCoverage (fun _ => True)

/-- `institutionLinkFromTeachingGrant`, omit the old link
`ChurchFoundedInCommissionedApostles`: the table powers were given, nothing is
founded in the mandate. -/
def omitLinkInstitution : Prop :=
  ¬ ChurchFoundedInCommissionedApostles (unitSig True) (unitAgency True True False False)
      ⟨tableGov⟩ ∧
    SelectedGoverningWithinTableOrTeaching tableGov ∧
    TeachingGrantFoundsInMandate (unitSig True) (unitAgency True True False False) ⟨tableGov⟩ ∧
    ¬ InstitutionLinkFor (unitSig True) (unitAgency True True False False) ⟨tableGov⟩ tableGov

/-- `institutionLinkFromTeachingGrant`, omit
`SelectedGoverningWithinTableOrTeaching`: baptizing selected and given. -/
def omitWithinInstitution : Prop :=
  ChurchFoundedInCommissionedApostles (unitSig True) (unitAgency True True False False)
      ⟨fun p => p = .baptize⟩ ∧
    ¬ SelectedGoverningWithinTableOrTeaching (fun p => p = .baptize) ∧
    TeachingGrantFoundsInMandate (unitSig True) (unitAgency True True False False)
      ⟨fun p => p = .baptize⟩ ∧
    ¬ InstitutionLinkFor (unitSig True) (unitAgency True True False False)
      ⟨fun p => p = .baptize⟩ (fun p => p = .baptize)

/-- `institutionLinkFromTeachingGrant`, omit `TeachingGrantFoundsInMandate`:
teaching selected and given, commissioning to teach without founding in the
mandate. -/
def omitGrantInstitution : Prop :=
  ChurchFoundedInCommissionedApostles (unitSig True) (unitAgency True True False True) ⟨teachGov⟩ ∧
    SelectedGoverningWithinTableOrTeaching teachGov ∧
    ¬ TeachingGrantFoundsInMandate (unitSig True) (unitAgency True True False True) ⟨teachGov⟩ ∧
    ¬ InstitutionLinkFor (unitSig True) (unitAgency True True False True) ⟨teachGov⟩ teachGov

/-- Map 2 witness: the teaching-inclusive predicate, every power given, a held
mandate, founding in the mandate and the teaching commission. -/
def witnessGovernance : Prop :=
  (∃ g, (unitAgency True True True True).HoldsMandate (unitSig True).jesus g) ∧
    SelectedGoverningIncludesTeaching inclusiveGov ∧ TableGoverningIsSelected inclusiveGov ∧
    SelectedGoverningWithinTableOrTeaching inclusiveGov ∧
    TeachingGrantFoundsInMandate (unitSig True) (unitAgency True True True True) ⟨fun _ => True⟩ ∧
    ChurchFoundedInCommissionedApostles (unitSig True) (unitAgency True True True True)
      ⟨fun _ => True⟩ ∧
    NarrowGovernanceCriterionFails inclusiveGov ∧
    TeachingInclusiveGovernanceCriterion inclusiveGov ∧ NamedGovernanceCoverage inclusiveGov ∧
    InstitutionLinkFor (unitSig True) (unitAgency True True True True) ⟨fun _ => True⟩ inclusiveGov

/-! ### Map 3: founding reading and attestation -/

/-- `immediateFailsFromEnvoyFounding`, omit the God-founded envoy witness:
nothing founded as teaching authority, nothing direct. -/
def omitEventImmediate : Prop :=
  ¬ GodFoundedSomeJesusEnvoySociety (unitSig False) (unitAgency False True False False) ∧
    DirectExcludesJesusEnvoy (unitSig False) (unitAgency False True False False)
      (fun _ _ => False) ∧
    ¬ ImmediateReadingFails (unitSig False) (unitAgency False True False False)
      (fun _ _ => False)

/-- `immediateFailsFromEnvoyFounding`, omit `DirectExcludesJesusEnvoy`: every
founding is direct and an envoy event. -/
def omitExclusionImmediate : Prop :=
  GodFoundedSomeJesusEnvoySociety (unitSig True) (unitAgency True True True True) ∧
    ¬ DirectExcludesJesusEnvoy (unitSig True) (unitAgency True True True True)
      (fun _ _ => True) ∧
    ¬ ImmediateReadingFails (unitSig True) (unitAgency True True True True) (fun _ _ => True)

/-- `johnIndependentFromStrands`, omit the strand premise: no pair independent. -/
def omitStrandsJohn : Prop :=
  ¬ JohannineSayingsIndependentOfMatthean noneIndependent ∧
    ¬ JohnCommissionIndependent noneIndependent

/-- Map 3 witness: the God founded the envoy society as teaching authority, no
founding is direct; every pair of distinct reports is independent. -/
def witnessFounding : Prop :=
  GodFoundedSomeJesusEnvoySociety (unitSig True) (unitAgency True True True True) ∧
    DirectExcludesJesusEnvoy (unitSig True) (unitAgency True True True True)
      (fun _ _ => False) ∧
    ImmediateReadingFails (unitSig True) (unitAgency True True True True) (fun _ _ => False) ∧
    JohannineSayingsIndependentOfMatthean allIndependent ∧
    JohnCommissionIndependent allIndependent

/-- All controls of round 6. -/
def Certificate : Prop :=
  omitVisibleJoint ∧ omitSpiritualJoint ∧ omitBothJoint ∧
    omitVisibleVisible ∧ omitBothVisible ∧ omitVisSpiritualVisible ∧
    omitVisibleFails ∧ omitInvisibleFails ∧
    omitVisibleCoverage ∧ omitSpiritualCoverage ∧ omitBothCoverage ∧ witnessChurch ∧
    omitTeachNarrow ∧ omitTeachInclusive ∧ omitTableInclusive ∧ omitWithinInclusive ∧
    omitTableCoverage ∧ omitWithinCoverage ∧
    omitLinkInstitution ∧ omitWithinInstitution ∧ omitGrantInstitution ∧ witnessGovernance ∧
    omitEventImmediate ∧ omitExclusionImmediate ∧ omitStrandsJohn ∧ witnessFounding

end Control

end TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks
