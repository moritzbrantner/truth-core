import TruthCore.Causality.UnderivedEssenceEsse
import TruthCore.Results.Logic.ExcludedMiddleIffDne.Solution
import TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.Solution
namespace TruthCore.Results.Causality.UnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.UnderivedCommonSource
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedEssenceEsse
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- The sufficient relation interface is restricted to q3 causes in the
esse respect. It says nothing about unrelated ordinary event causes. -/
theorem actual_not_not_identity_direct {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A) (n : B)
    (hn : m.ExistsAt w n) (hNoSupport : ∀ c, m.ExistsAt w c → ¬R w c n)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    ¬¬p.esseOf n = p.essenceOf n := by
  intro hDistinct
  have hExternal :=
    TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.distinctEsseExternalFromExhaustion
      p hExhaustive hNoSelfCause
  obtain ⟨c, hc, _, hCause⟩ := hExternal n ⟨hInAct n hn, hDistinct⟩
  have hExists := hPresent c n hn hc hCause
  exact hNoSupport c hExists (hTyped c n hExists hn hc hCause)

/-- Promote the constructive q3 consequence for this same named individual
using explicitly supplied excluded middle. Target existence and world-local
support absence remain separate; no necessary→underived inference is used. -/
theorem actual_identity_direct {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A) (n : B)
    (hn : m.ExistsAt w n) (hNoSupport : NoExistingSupportAt m R w n)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    p.esseOf n = p.essenceOf n := by
  exact
    (TruthCore.Results.Logic.ExcludedMiddleIffDne.excludedMiddleIffDoubleNegationElimination.mp hEM)
      _ (actual_not_not_identity_direct m R w p n hn hNoSupport
        hInAct hPresent hTyped hExhaustive hNoSelfCause)

/-- Retain the exact five original #495 union-route premises, plus the two
q3 premises and THREE open selected-world adapters. The ordinary Causes
relation does not occur in these additional assumptions. -/
theorem from_union_direct {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hNecessary : NecessaryBeing m w) (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    UnderivedEssenceIdentity m R w p := by
  obtain ⟨n, hn, hNecessaryN, hNoSupport⟩ :=
    TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
      m R w hNecessary hReflexive hNoContingent hUnionWF hEM
  refine ⟨n, ⟨hn, hNecessaryN, hNoSupport⟩, ?_⟩
  exact actual_identity_direct m R w p n hn (hNoSupport w) hEM
    hInAct hPresent hTyped hExhaustive hNoSelfCause

/-- Constructive core: actual absence of R-support, rather than modality, does
work here. Apply the existing q.3 a.4 conditional, then transport its actual
cause through the explicitly open interfaces. No double-negation elimination. -/
theorem actual_not_not_identity {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A) (n : B)
    (hn : m.ExistsAt w n) (hNoSupport : ∀ c, m.ExistsAt w c → ¬R w c n)
    (hMap : ActualCauseSupportsEsse m R w)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hActual : UnitingCausesAreActual m p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    ¬¬p.esseOf n = p.essenceOf n := by
  exact actual_not_not_identity_direct m R w p n hn hNoSupport hInAct hPresent
    (fun c x hc hx hne hCause => hMap c x hc hx (hActual c x hc hx hne hCause))
    hExhaustive hNoSelfCause

/-- Retain all FIVE original #495 union-route premises and its exact witness.
The six additional premises are open interfaces plus q.3 a.4's two source
commitments. Neither pure actuality nor uniqueness is concluded. -/
theorem from_union {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hNecessary : NecessaryBeing m w) (hReflexive : ActualReflexive m w)
    (hNoContingent : NoContingentGroundOfNecessary m R w)
    (hUnionWF : WellFoundedUnionNecessarySupport m R w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hMap : ActualCauseSupportsEsse m R w)
    (hInAct : ExistingInActAt m p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m p.CausesIn p.esse w)
    (hActual : UnitingCausesAreActual m p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    UnderivedEssenceIdentity m R w p := by
  exact from_union_direct m R w p hNecessary hReflexive hNoContingent hUnionWF hEM
    hInAct hPresent
    (fun c x hc hx hne hCause => hMap c x hc hx (hActual c x hc hx hne hCause))
    hExhaustive hNoSelfCause

theorem controls : Controls := by
  let m := TruthCore.Models.NecessarilyUnderived.varying
  have hNec (x : Bool) : NecessaryAt m true x := by intro _ _; trivial
  have hMap : ActualCauseSupportsEsse m m.Causes true := by
    intro _ _ _ _ h; exact h
  have hNamed : NamedNecessarilyUnderived m m.Causes true false := by
    refine ⟨True.intro, hNec false, ?_⟩
    intro v c _ h
    cases h.2.2
  have hPairCoherent : Coherent pairProfile := by
    intro _ _ _; exact ⟨True.intro, True.intro⟩
  have hPairDichotomy : DistinctEsseCauseDichotomyReading pairProfile := by
    intro x h
    cases x with
    | false => exact False.elim (h.2 rfl)
    | true => exact Or.inr ⟨false, Bool.noConfusion, True.intro, rfl, rfl⟩
  have hPairNoSelf : EssentialPrinciplesCannotCauseDistinctEsseReading pairProfile :=
    fun _ _ h => h
  have hPairInAct : ExistingInActAt m pairProfile.InAct () true :=
    fun _ _ => True.intro
  have hPairPresent : UnitingCausesPresent m pairProfile.CausesIn () true :=
    fun _ _ _ _ _ => True.intro
  have hPairActual : UnitingCausesAreActual m pairProfile.CausesIn () true := by
    intro c x _ _ _ h
    exact ⟨rfl, h⟩
  refine ⟨(by intro _ _; trivial), (by intro _ _; trivial), ?_, ?_, ?_, ?_⟩
  · intro w
    have hSub : Subrelation (PresentEsseSupport m m.Causes w)
        (UnionNecessarySupport m m.Causes false) := by
      intro c x h
      exact ⟨(by intro _ _; trivial), (by intro _ _; trivial), w, h.1, h.2⟩
    exact hSub.wf TruthCore.Models.NecessarilyUnderived.varyingUnionWellFounded
  · refine ⟨hPairCoherent, hPairDichotomy, hPairNoSelf, hPairInAct,
      hPairPresent, hPairActual, hMap, hNamed, rfl, hNec true,
      ⟨false, Bool.noConfusion, True.intro, rfl, rfl⟩,
      ⟨True.intro, Bool.noConfusion⟩, ?_⟩
    intro h
    exact h.2.2 true false True.intro ⟨rfl, rfl, rfl⟩
  · refine ⟨(fun _ _ h => h.elim), ?_, (fun _ _ h => h),
      (fun _ _ _ _ h => h.elim), (fun _ _ _ _ _ h => h.elim),
      hMap, hNamed, ?_, Bool.noConfusion⟩
    · intro x h
      cases x with
      | false => cases h.1
      | true => exact False.elim (h.2 rfl)
    · intro h
      exact Bool.noConfusion (h false True.intro)
  · refine ⟨hPairCoherent, hPairDichotomy, hPairNoSelf, hPairInAct,
      hPairPresent, hPairActual, ?_, ?_, Bool.noConfusion⟩
    · exact ⟨True.intro, hNec true, fun _ _ _ h => h⟩
    · intro h
      exact h false true True.intro True.intro ⟨rfl, rfl, rfl⟩

theorem typed_correspondence_control : TypedCorrespondenceControl := by
  refine ⟨(fun _ _ _ => ⟨True.intro, True.intro⟩), ?_, (fun _ _ h => h),
    (fun _ _ => True.intro), (fun _ _ _ _ _ => True.intro),
    (fun _ _ _ _ _ h => h), (fun _ _ _ _ _ h => Or.inl h), ?_, ?_, ?_, ?_⟩
  · intro x h
    cases x with
    | none => exact False.elim (h.2 rfl)
    | some b =>
      cases b with
      | false => exact Or.inr ⟨none, (by intro h; cases h), True.intro, rfl, rfl⟩
      | true => exact False.elim (h.2 rfl)
  · intro h
    have hBad := h (some false) (some true) True.intro True.intro
      (Or.inr ⟨rfl, rfl⟩)
    cases hBad.1
  · have hSub : Subrelation
        (UnionNecessarySupport typedOnlyOntic typedOnlySupport ())
        (fun c x => typedOnlyRank c < typedOnlyRank x) := by
      intro c x h
      obtain ⟨_, _, _, _, hc, hx⟩ := h
      cases hc
      cases hx
      exact Nat.zero_lt_succ 0
    exact hSub.wf (InvImage.wf typedOnlyRank Nat.lt_wfRel.wf)
  · have hSub : Subrelation (typedOnlyOntic.Causes ())
        (fun c x => typedOnlyRank c < typedOnlyRank x) := by
      intro c x h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Nat.zero_lt_succ 0
      · exact Nat.lt_succ_self 1
    exact hSub.wf (InvImage.wf typedOnlyRank Nat.lt_wfRel.wf)
  · refine ⟨none, ⟨True.intro, (by intro _ _; trivial), ?_⟩, rfl⟩
    intro _ _ _ h
    cases h.2

theorem all_controls : ExtendedControls :=
  ⟨controls, typed_correspondence_control⟩
end TruthCore.Results.Causality.UnderivedEssenceEsse
