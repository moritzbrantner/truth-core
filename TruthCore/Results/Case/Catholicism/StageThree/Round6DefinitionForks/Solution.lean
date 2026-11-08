module

public import TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks

/-!
# Round 6: derivations of stage-3 definition-fork statements

Ten derivations from the open analyst premises of
`TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks`, and the omission
and nonvacuity controls. The derivations are zero-axiom.
-/

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.Round6DefinitionForks
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Case.Catholicism.StageThree.Commissions
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
open TruthCore.Case.Catholicism.StageThree.CommissionDefinitions
open TruthCore.Case.Catholicism.StageThree.FoundingDefinitions
open TruthCore.Case.Catholicism.StageThree.CommissionAttestation
open TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks
open TruthCore.Logic (ExcludedMiddle)

/-! ## Map 1: Church criteria -/

/-- The selected Church coextends with the visible-and-spiritual criterion: each
direction of the iff comes from a separate inclusion premise. -/
theorem churchJointFromAspects (σ : Signature) (church spiritual : σ.Society → Prop)
    (hVisible : SelectedChurchIsVisible σ church)
    (hSpiritual : SelectedChurchIsSpiritual σ church spiritual)
    (hBoth : VisibleSpiritualSocietyIsChurch σ church spiritual) :
    JointAspectCriterion σ church spiritual := by
  intro c
  constructor
  · intro hc
    exact ⟨hVisible c hc, hSpiritual c hc⟩
  · rintro ⟨hv, hs⟩
    exact hBoth c hv hs

/-- The selected Church coextends with the visible criterion: the Church is
visible, and a visible society is spiritual and hence (being visible and
spiritual) the Church. The spiritual-community predicate is the middle term. -/
theorem churchVisibleFromAspects (σ : Signature) (church spiritual : σ.Society → Prop)
    (hVisible : SelectedChurchIsVisible σ church)
    (hBoth : VisibleSpiritualSocietyIsChurch σ church spiritual)
    (hVisSpiritual : VisibleSocietyIsSpiritual σ spiritual) :
    VisibleCriterion σ church := by
  intro c
  constructor
  · intro hc
    exact hVisible c hc
  · intro hv
    have hs : spiritual c := hVisSpiritual c hv
    exact hBoth c hv hs

/-- The spiritual calibration is false: an invisible spiritual community would
be the Church under it, but the Church is visible. -/
theorem spiritualFailsFromInvisibleCommunion (σ : Signature) (church spiritual : σ.Society → Prop)
    (hVisible : SelectedChurchIsVisible σ church)
    (hInvisible : SomeSpiritualCommunityNotVisible σ spiritual) :
    SpiritualCriterionFails σ church spiritual := by
  intro hCrit
  obtain ⟨c, hs, hNotVisible⟩ := hInvisible
  have hc : church c := (hCrit c).mpr hs
  exact hNotVisible (hVisible c hc)

/-- Named coverage of the Church fork holds through its joint case. -/
theorem namedChurchCoverageFromAspects (σ : Signature) (church spiritual : σ.Society → Prop)
    (hVisible : SelectedChurchIsVisible σ church)
    (hSpiritual : SelectedChurchIsSpiritual σ church spiritual)
    (hBoth : VisibleSpiritualSocietyIsChurch σ church spiritual) :
    NamedChurchCoverage σ church spiritual := by
  have hJoint := churchJointFromAspects σ church spiritual hVisible hSpiritual hBoth
  exact Or.inr (Or.inr hJoint)

/-! ## Map 2: governing criteria -/

/-- The narrow calibration is false: it would make teaching governing in the
fixed table, where it is not. -/
theorem narrowFailsFromTeaching (governing : Power → Prop)
    (hTeach : SelectedGoverningIncludesTeaching governing) :
    NarrowGovernanceCriterionFails governing := by
  intro hNarrow
  have hTable : Power.teach.Governing = true := (hNarrow .teach).mp hTeach
  exact Bool.noConfusion hTable

/-- The selected governing predicate is the teaching-inclusive criterion, from
its two inclusions in the table-or-teaching extension and the inclusion of
teaching. -/
theorem teachingInclusiveFromBounds (governing : Power → Prop)
    (hTeach : SelectedGoverningIncludesTeaching governing)
    (hTable : TableGoverningIsSelected governing)
    (hWithin : SelectedGoverningWithinTableOrTeaching governing) :
    TeachingInclusiveGovernanceCriterion governing := by
  intro p
  constructor
  · intro hp
    exact hWithin p hp
  · rintro (hp | rfl)
    · exact hTable p hp
    · exact hTeach

/-- Named governance coverage, without deciding whether teaching is governing:
by excluded middle on that question, the selected predicate is the
teaching-inclusive criterion or the narrow one. -/
theorem namedGovernanceCoverageFromBounds (governing : Power → Prop)
    (hEM : ExcludedMiddle)
    (hTable : TableGoverningIsSelected governing)
    (hWithin : SelectedGoverningWithinTableOrTeaching governing) :
    NamedGovernanceCoverage governing := by
  rcases hEM (governing .teach) with hTeach | hNoTeach
  · exact Or.inr (teachingInclusiveFromBounds governing hTeach hTable hWithin)
  · refine Or.inl (fun p => ⟨fun hp => ?_, hTable p⟩)
    rcases hWithin p hp with h | rfl
    · exact h
    · exact absurd hp hNoTeach

/-- The criterion-matched institutional link: a selected governing power is a
table power (old link, first clause) or teaching (teaching-grant bridge); the
teaching commission is the old link's second clause. -/
theorem institutionLinkFromTeachingGrant (σ : Signature) (A : Agency σ) (E : Commissioning)
    (governing : Power → Prop)
    (hLink : ChurchFoundedInCommissionedApostles σ A E)
    (hWithin : SelectedGoverningWithinTableOrTeaching governing)
    (hGrant : TeachingGrantFoundsInMandate σ A E) :
    InstitutionLinkFor σ A E governing := by
  intro g hm hf hv
  obtain ⟨hGov, hTeachCommission⟩ := hLink g hm hf hv
  refine ⟨fun p hp hGave => ?_, hTeachCommission⟩
  rcases hWithin p hp with hTableP | rfl
  · exact hGov p hTableP hGave
  · exact hGrant g hm hf hv hGave

/-! ## Map 3: founding reading and attestation -/

/-- The immediate-only reading fails: under it the God-founded envoy society
would be founded directly, which the exclusion forbids for an envoy event. -/
theorem immediateFailsFromEnvoyFounding (σ : Signature) (A : Agency σ)
    (direct : σ.Being → σ.Society → Prop)
    (hEvent : GodFoundedSomeJesusEnvoySociety σ A)
    (hExclusion : DirectExcludesJesusEnvoy σ A direct) :
    ImmediateReadingFails σ A direct := by
  intro hImmediate
  obtain ⟨g, c, hGod, hEnvoy, hFounded⟩ := hEvent
  have hDirect : direct g c := (hImmediate g c hGod).mp hFounded
  exact hExclusion g c hGod hEnvoy hDirect

/-- John 20's commission saying is independent of Matthew 18's: John 20 is
Johannine and Matthew 18 Matthean in the fixed strand table. -/
theorem johnIndependentFromStrands (T : Tradition)
    (hStrands : JohannineSayingsIndependentOfMatthean T) :
    JohnCommissionIndependent T := by
  left
  exact hStrands .jn20 .mt18 rfl rfl

/-! ## Controls -/

section Controls
open TruthCore.Case.Catholicism.StageThree.Round6DefinitionForks.Control

theorem omitVisibleJoint_holds : omitVisibleJoint :=
  ⟨fun h => Bool.noConfusion (h .a rfl),
   fun c hc => hc,
   fun c hv _ => absurd hv (by cases c <;> decide),
   fun h => Bool.noConfusion ((h .a).mp rfl).1⟩

theorem omitSpiritualJoint_holds : omitSpiritualJoint :=
  ⟨fun c hc => hc,
   fun h => Bool.noConfusion (h .a rfl),
   fun c _ hs => absurd hs (by cases c <;> decide),
   fun h => Bool.noConfusion ((h .a).mp rfl).2⟩

theorem omitBothJoint_holds : omitBothJoint :=
  ⟨fun c hc => absurd hc (by cases c <;> decide),
   fun c hc => absurd hc (by cases c <;> decide),
   fun h => Bool.noConfusion (h .a rfl rfl),
   fun h => Bool.noConfusion ((h .a).mpr ⟨rfl, rfl⟩)⟩

theorem omitVisibleVisible_holds : omitVisibleVisible :=
  ⟨fun h => Bool.noConfusion (h .a rfl),
   fun c hv _ => absurd hv (by cases c <;> decide),
   fun c hv => absurd hv (by cases c <;> decide),
   fun h => Bool.noConfusion ((h .a).mp rfl)⟩

theorem omitBothVisible_holds : omitBothVisible :=
  ⟨fun c hc => absurd hc (by cases c <;> decide),
   fun h => Bool.noConfusion (h .a rfl rfl),
   fun c hv => hv,
   fun h => Bool.noConfusion ((h .a).mpr rfl)⟩

theorem omitVisSpiritualVisible_holds : omitVisSpiritualVisible :=
  ⟨fun c hc => absurd hc (by cases c <;> decide),
   fun c _ hs => absurd hs (by cases c <;> decide),
   fun h => Bool.noConfusion (h .a rfl),
   fun h => Bool.noConfusion ((h .a).mpr rfl)⟩

theorem omitVisibleFails_holds : omitVisibleFails :=
  ⟨fun h => Bool.noConfusion (h .a rfl),
   ⟨.a, rfl, fun h => Bool.noConfusion h⟩,
   fun h => h (fun _ => Iff.rfl)⟩

theorem omitInvisibleFails_holds : omitInvisibleFails :=
  ⟨fun c hc => hc,
   fun ⟨c, hs, hnv⟩ => hnv hs,
   fun h => h (fun _ => Iff.rfl)⟩

theorem omitVisibleCoverage_holds : omitVisibleCoverage :=
  ⟨fun h => Bool.noConfusion (h .b rfl),
   fun c _ => by cases c <;> rfl,
   fun c hv _ => by cases c <;> first | rfl | exact absurd hv (by decide),
   fun h => by
     rcases h with h | h | h
     · exact Bool.noConfusion ((h .b).mp rfl)
     · exact Bool.noConfusion ((h .c).mpr rfl)
     · exact Bool.noConfusion ((h .b).mp rfl).1⟩

theorem omitSpiritualCoverage_holds : omitSpiritualCoverage :=
  ⟨fun c _ => by cases c <;> rfl,
   fun h => Bool.noConfusion (h .b rfl),
   fun c _ hs => by cases c <;> first | rfl | exact absurd hs (by decide),
   fun h => by
     rcases h with h | h | h
     · exact Bool.noConfusion ((h .c).mpr rfl)
     · exact Bool.noConfusion ((h .b).mp rfl)
     · exact Bool.noConfusion ((h .b).mp rfl).2⟩

theorem omitBothCoverage_holds : omitBothCoverage :=
  ⟨fun c hc => absurd hc (by cases c <;> decide),
   fun c hc => absurd hc (by cases c <;> decide),
   fun h => Bool.noConfusion (h .a rfl rfl),
   fun h => by
     rcases h with h | h | h
     · exact Bool.noConfusion ((h .a).mpr rfl)
     · exact Bool.noConfusion ((h .a).mpr rfl)
     · exact Bool.noConfusion ((h .a).mpr ⟨rfl, rfl⟩)⟩

theorem witnessChurch_holds : witnessChurch :=
  ⟨⟨.a, rfl⟩,
   fun c hc => hc,
   fun c hc => by cases c <;> first | rfl | exact absurd hc (by decide),
   fun c hv _ => hv,
   fun c hv => by cases c <;> first | rfl | exact absurd hv (by decide),
   ⟨.b, rfl, fun h => Bool.noConfusion h⟩,
   fun c => by cases c <;> decide,
   fun _ => Iff.rfl,
   fun h => Bool.noConfusion ((h .b).mpr rfl),
   Or.inl (fun _ => Iff.rfl)⟩

theorem omitTeachNarrow_holds : omitTeachNarrow :=
  ⟨fun h => Bool.noConfusion h, fun h => h (fun _ => Iff.rfl)⟩

theorem omitTeachInclusive_holds : omitTeachInclusive :=
  ⟨fun h => Bool.noConfusion h, fun _ h => h, fun _ h => Or.inl h,
   fun h => Bool.noConfusion ((h .teach).mpr (Or.inr rfl))⟩

theorem omitTableInclusive_holds : omitTableInclusive :=
  ⟨rfl, fun h => Power.noConfusion (h .keys rfl), fun _ h => Or.inr h,
   fun h => Power.noConfusion ((h .keys).mpr (Or.inl rfl))⟩

theorem omitWithinInclusive_holds : omitWithinInclusive :=
  ⟨trivial, fun _ _ => trivial,
   fun h => by rcases h .baptize trivial with h | h <;> exact absurd h (by decide),
   fun h => by rcases (h .baptize).mp trivial with h | h <;> exact absurd h (by decide)⟩

theorem omitTableCoverage_holds : omitTableCoverage :=
  ⟨fun h => h .keys rfl, fun _ h => h.elim,
   fun h => by
     rcases h with h | h
     · exact (h .keys).mpr rfl
     · exact (h .keys).mpr (Or.inl rfl)⟩

theorem omitWithinCoverage_holds : omitWithinCoverage :=
  ⟨fun _ _ => trivial,
   fun h => by rcases h .baptize trivial with h | h <;> exact absurd h (by decide),
   fun h => by
     rcases h with h | h
     · exact Bool.noConfusion ((h .baptize).mp trivial)
     · rcases (h .baptize).mp trivial with h | h <;> exact absurd h (by decide)⟩

theorem omitLinkInstitution_holds : omitLinkInstitution :=
  ⟨fun h => (h false trivial trivial trivial).1 .keys rfl rfl,
   fun _ h => Or.inl h,
   fun _ _ _ _ h => Bool.noConfusion h,
   fun h => (h false trivial trivial trivial).1 .keys rfl rfl⟩

theorem omitWithinInstitution_holds : omitWithinInstitution :=
  ⟨fun _ _ _ _ => ⟨fun p hp hg => by subst hg; exact Bool.noConfusion hp,
     fun h => Power.noConfusion h⟩,
   fun h => by rcases h .baptize rfl with h | h <;> exact absurd h (by decide),
   fun _ _ _ _ h => Power.noConfusion h,
   fun h => (h false trivial trivial trivial).1 .baptize rfl rfl⟩

theorem omitGrantInstitution_holds : omitGrantInstitution :=
  ⟨fun _ _ _ _ => ⟨fun p hp hg => by subst hg; exact Bool.noConfusion hp, fun _ => trivial⟩,
   fun _ h => Or.inr h,
   fun h => h false trivial trivial trivial rfl,
   fun h => (h false trivial trivial trivial).1 .teach rfl rfl⟩

theorem witnessGovernance_holds : witnessGovernance :=
  ⟨⟨true, trivial⟩, Or.inr rfl, fun _ h => Or.inl h, fun _ h => h,
   fun _ _ _ _ _ => trivial,
   fun _ _ _ _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩,
   fun h => Bool.noConfusion ((h .teach).mp (Or.inr rfl)),
   fun _ => Iff.rfl, Or.inr (fun _ => Iff.rfl),
   fun _ _ _ _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

theorem omitEventImmediate_holds : omitEventImmediate :=
  ⟨fun ⟨_, _, _, _, h⟩ => h, fun _ _ _ _ h => h,
   fun h => h (fun _ _ _ => Iff.rfl)⟩

theorem omitExclusionImmediate_holds : omitExclusionImmediate :=
  ⟨⟨true, (), rfl, ⟨trivial, trivial⟩, trivial⟩,
   fun h => h true () rfl ⟨trivial, trivial⟩ trivial,
   fun h => h (fun _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)⟩

theorem omitStrandsJohn_holds : omitStrandsJohn :=
  ⟨fun h => h .jn20 .mt18 rfl rfl, fun h => by rcases h with h | h <;> exact h⟩

theorem witnessFounding_holds : witnessFounding :=
  ⟨⟨true, (), rfl, ⟨trivial, trivial⟩, trivial⟩,
   fun _ _ _ _ h => h,
   fun h => (h true () rfl).mp trivial,
   fun r₁ r₂ h₁ h₂ heq => by subst heq; rw [h₁] at h₂; exact Strand.noConfusion h₂,
   Or.inl CommissionReport.noConfusion⟩

theorem controls : Certificate :=
  ⟨omitVisibleJoint_holds, omitSpiritualJoint_holds, omitBothJoint_holds,
   omitVisibleVisible_holds, omitBothVisible_holds, omitVisSpiritualVisible_holds,
   omitVisibleFails_holds, omitInvisibleFails_holds,
   omitVisibleCoverage_holds, omitSpiritualCoverage_holds, omitBothCoverage_holds,
   witnessChurch_holds,
   omitTeachNarrow_holds, omitTeachInclusive_holds, omitTableInclusive_holds,
   omitWithinInclusive_holds, omitTableCoverage_holds, omitWithinCoverage_holds,
   omitLinkInstitution_holds, omitWithinInstitution_holds, omitGrantInstitution_holds,
   witnessGovernance_holds,
   omitEventImmediate_holds, omitExclusionImmediate_holds, omitStrandsJohn_holds,
   witnessFounding_holds⟩

end Controls

end TruthCore.Results.Case.Catholicism.StageThree.Round6DefinitionForks
