module

public import TruthCore.Causality.SpineRivalsRootEsse

/-!
Rival survival certificates for twelve spine premises. Each registered theorem
checks one explicit interpretation: the rival holds together with every other
premise of the named consuming theorem, and that theorem's conclusion fails.
The unregistered `…_excludes` helpers show that each rival is incompatible with
its premise on the shared carrier. Nothing here establishes or refutes a
premise, and no interpretation is claimed metaphysically possible.
-/

@[expose] public section

namespace TruthCore.Results.Causality.SpineRivalsRootEsse

open TruthCore.Causality.SpineRivalsRootEsse
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround
  SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.NecessarilyUnderived (UnionNecessarySupport)
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Case.Catholicism

variable {W B R : Type}

/-! ## Each rival is incompatible with its premise -/

theorem onlyNonConcrete_excludes (m : Ontic W B) (concrete : B → Prop) (w : W)
    (h : OnlyNonConcreteExistAt m concrete w) : ¬ InhabitedConcreteAt m concrete w :=
  fun ⟨b, hc, he⟩ => h.2 b he hc

theorem bottomless_excludes (m : Profile W B) (w : W)
    (h : BottomlessActualGroundingAt m w) : ¬ WholeRosterNotTrapped m w := by
  obtain ⟨⟨x, hx⟩, hAll⟩ := h
  intro hWhole
  refine hWhole ⟨⟨x, hx⟩, Set.mem_univ _⟩ ⟨?_, ?_⟩
  · intro e _ hSource
    obtain ⟨y, hy⟩ := hAll e.1 e.2
    exact hSource ⟨⟨y, hy.1, hy.2.1⟩, hy.2.2⟩
  · intro g _ _
    obtain ⟨y, hy⟩ := g.2
    exact ⟨y, hy, Set.mem_univ _⟩

theorem contingentRoot_excludes (m : Profile W B) (w : W)
    (h : ContingentRootAt m w) : ¬ EveryContingentGroundedAt m w := by
  obtain ⟨x, hr, hc⟩ := h
  intro hG
  obtain ⟨y, hy⟩ := hG x hr.1.1 hr.1.2 hc
  exact hr.2 y hy

theorem idleMaximum_excludes (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : SomeMaximumLeavesBeingToAnother InAct MoreIn CausesIn esse) :
    ¬ MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := by
  obtain ⟨m, x, _, hmax, hne, hx, hnot, _⟩ := h
  exact fun hG => hnot (hG m hmax x hne hx)

theorem thinExistence_excludes (m : Ontic W B) (InAct : B → R → Prop) (esse : R) (w : W)
    (h : ExistenceWithoutActOfBeingAt m InAct esse w) : ¬ ExistingInActAt m InAct esse w := by
  obtain ⟨⟨x, hx⟩, hno⟩ := h
  exact fun hE => hno x hx (hE x hx)

theorem nonConcreteEsseCause_excludes (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (esse : R)
    (h : SomeEsseCauseNonConcrete m w CausesIn esse) :
    ¬ EsseCauseIsActualConcreteGround m w CausesIn esse := by
  obtain ⟨c, x, hne, hx, hc, _, hnc⟩ := h
  exact fun hE => hnc (hE c x hne hx hc).1

theorem unboundedGrades_exclude (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (h : EveryActualGradeExceededAtBeing InAct MoreIn esse) :
    ¬ GradesToMaximumAtBeing InAct MoreIn esse := by
  obtain ⟨hcmp, hall⟩ := h
  intro hG
  obtain ⟨n, hn, hmax⟩ := hG hcmp
  obtain ⟨y, _, hy⟩ := hall n hn
  exact hmax y hy

theorem mereConservation_excludes (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (h : UniversalCauseLeavesPerfectionToSecondary InAct CausesIn esse) :
    ¬ UniversalCauseTransfersPerfections InAct CausesIn esse := by
  obtain ⟨c, x, r, _, hall, hne, hesse, hact, hnot, _⟩ := h
  exact fun hT => hnot (hT c hall x r hne hesse hact)

theorem abstractPrior_excludes (m : Profile W B) (w : W) (PriorSimply : B → B → Prop)
    (h : SomeSimplyPriorNonConcrete m w PriorSimply) :
    ¬ SimplyPriorIsActualConcreteGround m w PriorSimply := by
  obtain ⟨y, x, hne, hp, _, hnc⟩ := h
  exact fun hS => hnc (hS y x hne hp).1

theorem exceededGod_excludes (IsGod : B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (h : SomeGodExceededInBeing IsGod InAct MoreIn esse) :
    ¬ GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  obtain ⟨g, y, hg, _, _, hmore⟩ := h
  exact fun hM => (hM g hg).2 y hmore

theorem contingentSupport_excludes (m : Profile W B) (w : W)
    (h : SomeNecessaryConcretumContingentlySupported m w) :
    ¬ NoContingentConcreteSupport m w := by
  obtain ⟨v, a, b, ha, hb, hea, hnb, hg, u, hu, hna⟩ := h
  exact fun hN => hna (hN v ⟨a, ha⟩ ⟨b, hb⟩ hea hnb hg u hu)

theorem mutualSupport_excludes (m : Profile W B) (w : W)
    (h : NecessaryConcretaMutualSupport m w) : ¬ ConcreteNecessaryUnionWF m w := by
  obtain ⟨a, b, v, u, ha, hb, hna, hnb, hea, hab, heb, hba⟩ := h
  intro hWF
  have hAB : UnionNecessarySupport (concreteOntic m) (concreteSupport m) w ⟨a, ha⟩ ⟨b, hb⟩ :=
    ⟨hna, hnb, v, hea, hab⟩
  have hBA : UnionNecessarySupport (concreteOntic m) (concreteSupport m) w ⟨b, hb⟩ ⟨a, ha⟩ :=
    ⟨hnb, hna, u, heb, hba⟩
  have key : ∀ x y : {b // m.concrete b},
      UnionNecessarySupport (concreteOntic m) (concreteSupport m) w x y →
      UnionNecessarySupport (concreteOntic m) (concreteSupport m) w y x → False := by
    intro x
    induction x using hWF.induction with
    | _ x ih => exact fun y hxy hyx => ih y hyx x hyx hxy
  exact key _ _ hAB hBA

/-! ## Survival certificates -/

theorem em : ExcludedMiddle := fun p => Classical.em p

theorem tf : ¬ (true = false) := by decide
theorem ft : ¬ (false = true) := by decide

open Control

theorem abstractOnlySurvives : AbstractOnlySurvives := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ h => h⟩, em, ?_⟩
  rintro (⟨_, hc, _⟩ | ⟨_, _, hr, _⟩ | hnwf)
  · exact hc
  · exact hr.1.1
  · exact hnwf ⟨fun a => a.2.1.elim⟩

theorem bottomlessSurvives : BottomlessSurvives := by
  refine ⟨⟨⟨0, trivial, rfl⟩, fun x _ => ⟨x + 1, trivial, rfl, rfl⟩⟩, ⟨0, trivial, rfl⟩, ?_, em, ?_⟩
  · intro x _ _ _
    exact ⟨x + 1, trivial, rfl, rfl⟩
  · rintro ⟨_, _, _, hn⟩
    exact tf (hn true trivial)

theorem contingentRootSurvives : ContingentRootSurvives := by
  have hRoot : ActualRoot bruteRoot false () := ⟨⟨trivial, rfl⟩, fun _ h => h.2.2⟩
  refine ⟨⟨(), hRoot, rfl, true, trivial, tf⟩, ⟨(), hRoot, fun _ _ => rfl⟩, em, ?_⟩
  rintro ⟨_, _, hn, _⟩
  exact tf (hn true trivial)

theorem topIsMaximum : IsMaximumIn tierAct tierMore () Tier.top :=
  ⟨trivial, fun y h => by cases y <;> simp [tierMore, tierRank] at h⟩

theorem idleMaximumSurvives : IdleMaximumSurvives := by
  refine ⟨⟨.top, .made, .maker, topIsMaximum, by decide, trivial, ?_, by decide, by decide,
    rfl, rfl⟩, ⟨.top, topIsMaximum⟩, ?_⟩
  · intro h
    simp [tierCause] at h
  · rintro ⟨m, hmax, hall⟩
    cases m
    · have h := hall .made (by decide) trivial
      simp [tierCause] at h
    · exact hmax.2 .top (by simp [tierMore, tierRank])
    · exact hmax.2 .top (by simp [tierMore, tierRank])

theorem thinExistenceSurvives : ThinExistenceSurvives := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ h => h⟩, fun _ _ _ => trivial, ?_⟩
  intro h
  obtain ⟨_, hr⟩ := h () () trivial
  exact hr

theorem nonConcreteEsseCauseSurvives : NonConcreteEsseCauseSurvives := by
  refine ⟨⟨false, true, by decide, ⟨rfl, Or.inr rfl⟩, ⟨rfl, rfl⟩, Or.inl rfl, ft⟩,
    fun x hx _ => hx.1, ?_, ?_⟩
  · intro x hx
    refine ⟨false, ?_, rfl, hx⟩
    intro h
    subst h
    exact ft hx
  · intro h
    obtain ⟨_, _, _, hg⟩ := h true rfl (Or.inr rfl)
      ⟨Or.inr rfl, true, trivial, fun he => he.elim tf tf⟩
    exact hg

theorem unboundedGradesSurvive : UnboundedGradesSurvive := by
  have hRoot : ∀ k : Nat, ActualRoot ascent () k := fun _ => ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩
  refine ⟨⟨⟨1, 0, Nat.zero_lt_one⟩, fun n _ => ⟨n + 1, trivial, Nat.lt_succ_self n⟩⟩,
    ⟨0, ⟨⟨trivial, trivial⟩, Relation.ReflTransGen.refl⟩, fun _ _ => trivial, fun _ h => h.2.2⟩,
    em, fun m hmax => (hmax.2 (m + 1) (Nat.lt_succ_self m)).elim, fun _ _ => trivial,
    fun _ _ _ _ h => h.elim, ?_⟩
  rintro ⟨n, _, _, huniq⟩
  have h0 : 0 = n := huniq 0 (hRoot 0)
  have h1 : 1 = n := huniq 1 (hRoot 1)
  omega

theorem topCausesAllBeing : CausesAllInGenus conserveAct conserveCause false Tier.top :=
  fun _ hx _ => Or.inl ⟨rfl, rfl, hx⟩

theorem mereConservationSurvives : MereConservationSurvives := by
  refine ⟨⟨.top, .made, true, .maker, topCausesAllBeing, by decide,
    Or.inl ⟨rfl, rfl, by decide⟩, trivial, ?_, by decide, Or.inr ⟨rfl, rfl, rfl⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    simp [conserveCause] at h
  · intro c hn x r hesse _
    rcases hesse with ⟨_, hc, _⟩ | ⟨h, _⟩
    · subst hc
      exact (hn topCausesAllBeing).elim
    · exact (ft h).elim
  · intro c r hself _
    rcases hself with ⟨_, hc, hx⟩ | ⟨h, _⟩
    · exact (hx hc).elim
    · exact (ft h).elim
  · intro h
    have h' := h .top .made true (Or.inl ⟨rfl, rfl, by decide⟩) trivial
    simp [conserveCause] at h'

theorem abstractPriorSurvives : AbstractPriorSurvives := by
  refine ⟨⟨false, true, by decide, ⟨rfl, rfl⟩, ⟨rfl, trivial⟩, ft⟩, ⟨true, rfl, trivial⟩, ?_, ?_,
    em, ?_⟩
  · intro _ htrap
    exact htrap.1 ⟨true, rfl, trivial⟩ (Set.mem_univ _) (fun ⟨_, h⟩ => h)
  · intro x _ _ hc
    obtain ⟨_, _, _, h⟩ := hc
    exact (h trivial).elim
  · rintro ⟨n, hr, _, hfirst⟩
    have hn : n = true := hr.1.1
    subst hn
    exact ft (hfirst false ⟨rfl, rfl⟩)

theorem exceededGodSurvives : ExceededGodSurvives := by
  refine ⟨⟨true, false, rfl, trivial, ft, rfl, rfl⟩, ?_, fun _ _ _ _ h => h,
    fun h => h true rfl rfl⟩
  intro x hx
  refine ⟨false, ?_, rfl, hx⟩
  intro h
  subst h
  exact ft hx

theorem contingentSupportSurvives : ContingentSupportSurvives := by
  refine ⟨⟨true, .there, .whole, trivial, trivial, Or.inr (Or.inr ⟨rfl, rfl⟩),
    fun _ _ => Or.inl rfl, Or.inr ⟨rfl, rfl, rfl⟩, false, trivial, ?_⟩,
    ⟨.whole, trivial, Or.inl rfl⟩, ?_, ?_, trivial, ?_, em, ?_⟩
  · intro h
    simp [sustainedWhole] at h
  · have hw : ∀ h, Acc (fun a b : {x // ActualConcrete sustainedWhole false x} =>
        sustainedWhole.grounds false a.1 b.1) ⟨.whole, h⟩ :=
      fun h => ⟨_, fun y hy => by simp [sustainedWhole] at hy⟩
    refine ⟨fun ⟨a, ha⟩ => ⟨_, fun ⟨y, hyA⟩ hy => ?_⟩⟩
    have hy' : (false = false ∧ y = .whole ∧ a = .here) ∨
        (false = true ∧ y = .there ∧ a = .whole) := hy
    rcases hy' with ⟨_, hyw, _⟩ | ⟨h, _⟩
    · subst hyw
      exact hw hyA
    · exact (ft h).elim
  · intro x _ he hc
    cases x
    · obtain ⟨_, _, _, hnot⟩ := hc
      exact (hnot (Or.inl rfl)).elim
    · exact ⟨.whole, trivial, Or.inl rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · simp [sustainedWhole] at he
  · refine ⟨fun a => ⟨_, fun y hy => ?_⟩⟩
    obtain ⟨hny, hna, v, _, hg⟩ := hy
    obtain ⟨a, _⟩ := a
    obtain ⟨y, _⟩ := y
    have hg' : (v = false ∧ y = .whole ∧ a = .here) ∨
        (v = true ∧ y = .there ∧ a = .whole) := hg
    rcases hg' with ⟨_, _, hah⟩ | ⟨_, hyt, _⟩
    · subst hah
      have h := hna true trivial
      simp [concreteOntic, sustainedWhole] at h
    · subst hyt
      have h := hny false trivial
      simp [concreteOntic, sustainedWhole] at h
  · rintro ⟨b, _, _, hnec, hno⟩
    cases b
    · exact hno true .there trivial (Or.inr (Or.inr ⟨rfl, rfl⟩)) (Or.inr ⟨rfl, rfl, rfl⟩)
    · have h := hnec true trivial
      simp [sustainedWhole] at h
    · have h := hnec false trivial
      simp [sustainedWhole] at h

theorem mutualSupportSurvives : MutualSupportSurvives := by
  refine ⟨⟨false, true, false, true, trivial, trivial, fun _ _ => trivial, fun _ _ => trivial,
    trivial, Or.inl ⟨rfl, rfl, rfl⟩, trivial, Or.inr ⟨rfl, rfl, rfl⟩⟩,
    ⟨false, trivial, trivial⟩, ?_, ?_, trivial, fun _ _ _ _ _ _ _ _ => trivial, em, ?_⟩
  · have hf : ∀ h, Acc (fun a b : {x // ActualConcrete mutualPair false x} =>
        mutualPair.grounds false a.1 b.1) ⟨false, h⟩ :=
      fun h => ⟨_, fun y hy => by simp [mutualPair] at hy⟩
    refine ⟨fun ⟨a, ha⟩ => ⟨_, fun ⟨y, hyA⟩ hy => ?_⟩⟩
    have hy' : (false = false ∧ y = false ∧ a = true) ∨
        (false = true ∧ y = true ∧ a = false) := hy
    rcases hy' with ⟨_, hyf, _⟩ | ⟨h, _⟩
    · subst hyf
      exact hf hyA
    · exact (ft h).elim
  · intro x _ _ hc
    obtain ⟨_, _, _, h⟩ := hc
    exact (h trivial).elim
  · rintro ⟨b, _, _, _, hno⟩
    cases b
    · exact hno true true trivial trivial (Or.inr ⟨rfl, rfl, rfl⟩)
    · exact hno false false trivial trivial (Or.inl ⟨rfl, rfl, rfl⟩)

end TruthCore.Results.Causality.SpineRivalsRootEsse
