import TruthCore.Explanation.JointCooperation
import TruthCore.Results.Explanation.UltimateAdequacy.Solution
import TruthCore.Results.Causality.JointGroups.Solution
namespace TruthCore.Results.Explanation.JointCooperation
open TruthCore.Explanation.JointCooperation
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section General
variable {B E G S : Type} {m : Exercise B E G S} {g : G} {a b : E}

theorem suffices_members (hs : m.jointlySufficient g) {s : S} (ha : m.allowed s)
    (ho : ∀ e ∈ m.groups.members g, m.occurs s e) : m.occurs s (m.groups.effect g) :=
  hs s ha ho

theorem rest_members {s : S} (ho : ∀ e ∈ (m.groups.contributors g \ {a}) ∪ m.groups.enablers g, m.occurs s e)
    (hb : m.occurs s a) : ∀ e ∈ m.groups.members g, m.occurs s e := by
  rintro e (he | he)
  · by_cases h : e = a
    · exact h ▸ hb
    · exact ho e (Or.inl ⟨he, h⟩)
  · exact ho e (Or.inr he)

theorem rest_other {s : S} (hb : b ∈ m.groups.contributors g) (hne : a ≠ b)
    (ho : ∀ e ∈ (m.groups.contributors g \ {a}) ∪ m.groups.enablers g, m.occurs s e) :
    m.occurs s b :=
  ho b (Or.inl ⟨hb, fun h => hne h.symm⟩)

theorem redundant_of (ha : a ∈ m.groups.contributors g) (hb : b ∈ m.groups.contributors g)
    (hne : a ≠ b) (hs : m.jointlySufficient g)
    (hf : ∀ s, m.allowed s → m.occurs s b → m.occurs s a) : m.redundant g a :=
  ⟨ha, fun s hal ho => hs s hal (rest_members ho (hf s hal (rest_other hb hne ho)))⟩

theorem redundant_of_necessary (ha : a ∈ m.groups.contributors g) (hs : m.jointlySufficient g)
    (hn : NecessaryIn m a) : m.redundant g a :=
  ⟨ha, fun s hal ho => hs s hal (rest_members ho (hn s hal))⟩

theorem not_both {e : E} (h : m.indispensable g e) (h' : m.redundant g e) : False :=
  h.2 h'.2

theorem variation_one (hb : b ∈ m.groups.contributors g) (hne : a ≠ b)
    (hs : m.jointlySufficient g) (h : m.indispensable g a) :
    ∃ s, m.allowed s ∧ m.occurs s b ∧ ¬ m.occurs s a ∧ ¬ m.occurs s (m.groups.effect g) := by
  have h2 := h.2
  unfold Exercise.suffices at h2
  push Not at h2
  obtain ⟨s, hal, ho, ht⟩ := h2
  exact ⟨s, hal, rest_other hb hne ho, fun hoa => ht (hs s hal (rest_members ho hoa)), ht⟩

theorem variation (hc : Coordinated m g a b) (hs : m.jointlySufficient g)
    (h : Needed m g a b) : TwoWayVariation m g a b :=
  ⟨variation_one hc.2.2.2.1 hc.2.2.2.2 hs h.1,
   variation_one hc.2.2.1 (Ne.symm hc.2.2.2.2) hs h.2⟩

theorem not_fit (hv : TwoWayVariation m g a b) : ¬ MutualFit m a b := by
  obtain ⟨⟨s, hal, hb, hna, _⟩, _⟩ := hv
  exact fun hf => hna ((hf s hal).2 hb)

theorem coexist (hc : Coordinated m g a b) : Coexist m a b :=
  ⟨(hc.1.2 g hc.2.1).2.1 a (Or.inl hc.2.2.1), (hc.1.2 g hc.2.1).2.1 b (Or.inl hc.2.2.2.1)⟩

theorem needed_or (ha : a ∈ m.groups.contributors g) (hb : b ∈ m.groups.contributors g) :
    NoCooperationNeeded m g a b ∨ Needed m g a b := by
  by_cases h1 : m.suffices ((m.groups.contributors g \ {a}) ∪ m.groups.enablers g) (m.groups.effect g)
  · exact Or.inl (Or.inl ⟨ha, h1⟩)
  by_cases h2 : m.suffices ((m.groups.contributors g \ {b}) ∪ m.groups.enablers g) (m.groups.effect g)
  · exact Or.inl (Or.inr ⟨hb, h2⟩)
  exact Or.inr ⟨⟨ha, h1⟩, ⟨hb, h2⟩⟩

theorem source_no_common_left (h : m.exercisedGroups.graph.Source a) : ¬ CommonSource m a b := by
  rintro ⟨c, _, hca, _⟩
  obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.1 hca
  exact h ⟨y, hy⟩

theorem source_no_common_right (h : m.exercisedGroups.graph.Source b) : ¬ CommonSource m a b := by
  rintro ⟨c, _, _, hcb, _⟩
  obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.1 hcb
  exact h ⟨y, hy⟩

theorem suffices_single {c x : E} (h : m.suffices {c} x) {s : S} (hal : m.allowed s)
    (hc : m.occurs s c) : m.occurs s x :=
  h s hal (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact hc)

end General

theorem coverage : Coverage := by
  intro B E G S m g a b hc hs
  have key : NoCooperationNeeded m g a b ∨
      (TwoWayVariation m g a b ∧ (CommonSource m a b ∨ BruteCoincidence m a b)) := by
    rcases needed_or hc.2.2.1 hc.2.2.2.1 with h | h
    · exact Or.inl h
    · have hv := variation hc hs h
      refine Or.inr ⟨hv, ?_⟩
      by_cases hk : CommonSource m a b
      · exact Or.inl hk
      · exact Or.inr ⟨coexist hc, not_fit hv, hk⟩
  refine ⟨?_, key⟩
  rcases key with h | ⟨_, h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem branch_costs : BranchCosts := by
  intro B E G S m g a b
  refine ⟨fun hc hs => ?_, ?_, source_no_common_left, source_no_common_right, ?_⟩
  · have hne := hc.2.2.2.2
    have ha := hc.2.2.1
    have hb := hc.2.2.2.1
    refine ⟨fun hf => ⟨redundant_of ha hb hne hs fun s hal => (hf s hal).2,
        redundant_of hb ha (Ne.symm hne) hs fun s hal => (hf s hal).1⟩,
      fun h => ⟨variation hc hs h, not_fit (variation hc hs h),
        fun hn => not_both h.1 (redundant_of_necessary ha hs hn),
        fun hn => not_both h.2 (redundant_of_necessary hb hs hn)⟩,
      redundant_of_necessary ha hs,
      fun hm s hal => hs s hal (fun e he => hm e he s hal),
      fun c hm s hal ho => hs s hal (fun e he => hm e he s hal ho),
      fun c hca hcb hac hbc s hal => ⟨fun hoa => suffices_single hcb hal (suffices_single hac hal hoa),
        fun hob => suffices_single hca hal (suffices_single hbc hal hob)⟩,
      fun c h hca hcb => ?_,
      fun c hn hca h => not_both h.1 (redundant_of_necessary ha hs fun s hal =>
        suffices_single hca hal (hn s hal))⟩
    obtain ⟨⟨s, hal, hob, hna, _⟩, ⟨t, hat, hoa, hnb, _⟩⟩ := variation hc hs h
    exact ⟨⟨t, hat, hoa, fun hoc => hnb (suffices_single hcb hat hoc)⟩,
      ⟨s, hal, hob, fun hoc => hna (suffices_single hca hal hoc)⟩⟩
  · exact fun ha hb s hal => ⟨fun _ => hb s hal, fun _ => ha s hal⟩
  · exact ⟨fun h s hal _ => h s hal, fun h s hal => h s hal (fun _ he => he.elim)⟩

theorem fit_exclusion : FitExclusionIsAtMostOne := by
  intro B E G S m g
  constructor
  · intro h a b ha hna hb hnb
    by_contra hne
    exact h a b ha hna hb hnb hne fun s hal => ⟨fun _ => hnb s hal, fun _ => hna s hal⟩
  · intro h a b ha hna hb hnb hne _
    exact hne (h a b ha hna hb hnb)

theorem core : IncompatibleCore := by
  intro B E G S m g a b hc hs hsrc h
  exact ⟨coexist hc, not_fit (variation hc hs h), source_no_common_left hsrc⟩

theorem modal_bridges : ModalBridges := by
  intro B E G S W m o w
  refine ⟨fun hw e hn s hal => ?_, fun hw e hn v hv => ?_, fun g a b hc hs h hn hw => ?_⟩
  · obtain ⟨v, hv, ht⟩ := hw s hal
    exact (ht e).2 (hn v hv)
  · obtain ⟨s, hal, ht⟩ := hw v hv
    exact (ht e).1 (hn s hal)
  · refine not_both h.1 (redundant_of_necessary hc.2.2.1 hs fun s hal => ?_)
    obtain ⟨v, hv, ht⟩ := hw s hal
    exact (ht a).2 (hn v hv)

theorem refl_source {A : Type} {K : Graph A} {c x : A} (hs : K.Source x)
    (h : Relation.ReflTransGen K.edge c x) : c = x := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨y, _, hy⟩
  · exact h.symm
  · exact (hs ⟨y, hy⟩).elim

theorem no_least {A : Type} {K : Graph A} {p q : A} (hp : K.Source p) (hq : K.Source q)
    (hne : p ≠ q) : ¬ ∃ s, least K s := by
  rintro ⟨s, hs⟩
  exact hne ((refl_source hp (hs p)).symm.trans (refl_source hq (hs q)))

/-! The same-space fit rival and its unsufficient variant. -/

theorem fit_actual (x : FitEvent) : fit.occurs fit.actual x := by
  cases x <;> first | trivial | rfl

theorem fit_coordinated : Coordinated fit .joint .l .r :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun e _ => fit_actual e, fit_actual _⟩⟩,
    trivial, Or.inl rfl, Or.inr rfl, by decide⟩

theorem fit_sufficient : fit.jointlySufficient .joint := fun _ _ _ => trivial

theorem fit_source_l : fit.exercisedGroups.graph.Source .l := by
  rintro ⟨y, g, _, he, _⟩
  cases g <;> cases he

theorem fit_source_r : fit.exercisedGroups.graph.Source .r := by
  rintro ⟨y, g, _, he, _⟩
  cases g <;> cases he

theorem fit_supply (x : FitEvent) : Supply fit.groups fitIntrinsic x := by
  have hl : Supply fit.groups fitIntrinsic .l := .intrinsic _ (Or.inl rfl)
  have hr : Supply fit.groups fitIntrinsic .r := .intrinsic _ (Or.inr rfl)
  have ht : Supply fit.groups fitIntrinsic .t := by
    refine Supply.joint (h := fit.groups) .joint trivial ?_
    rintro e (rfl | rfl)
    · exact hl
    · exact hr
  have he : Supply fit.groups fitIntrinsic .e := by
    refine Supply.joint (h := fit.groups) .free trivial ?_
    intro e (hh : e = .t)
    exact hh ▸ ht
  cases x <;> assumption

theorem fit_necessary_l : NecessaryIn fit .l := fun _ _ => trivial
theorem fit_necessary_r : NecessaryIn fit .r := fun _ _ => trivial
theorem fit_necessary_t : NecessaryIn fit .t := fun _ _ => trivial

theorem fit_fit : MutualFit fit .l .r := fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

theorem fit_redundant_l : fit.redundant .joint .l :=
  redundant_of_necessary (Or.inl rfl) fit_sufficient fit_necessary_l
theorem fit_redundant_r : fit.redundant .joint .r :=
  redundant_of_necessary (Or.inr rfl) fit_sufficient fit_necessary_r

theorem fit_not_brute : ¬ BruteCoincidence fit .l .r := fun h => h.2.1 fit_fit

theorem fit_rival : FitRival := by
  refine ⟨fit_coordinated, fit_sufficient, fit_fit, fit_redundant_l, fit_redundant_r,
    fit_necessary_l, fit_necessary_r, fit_necessary_t, fit_not_brute,
    source_no_common_left fit_source_l, ?_, trivial, ?_, fit_source_l, fit_source_r,
    fit_supply, no_least fit_source_l fit_source_r (by decide), fun _ _ _ => trivial,
    fun s _ => ⟨s, trivial, fun _ => Iff.rfl⟩, fun v _ => ⟨v, trivial, fun _ => Iff.rfl⟩,
    fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
    ⟨rfl, false, trivial, fun h => Bool.noConfusion h⟩,
    fun y x => ⟨fun h => h.2.2, fun h => ⟨fit_actual y, fit_actual x, h⟩⟩⟩
  · intro h
    exact Bool.noConfusion (h false trivial)
  · intro h
    have hh : false = true := h false trivial (fun e he => by
      rcases he with he | he
      · have he' : e = .t := he
        subst he'
        trivial
      · exact he.elim)
    exact Bool.noConfusion hh

theorem loose_coordinated : Coordinated loose .joint .l .r :=
  ⟨⟨trivial, fun g _ => ⟨trivial, fun e _ => by cases e <;> first | trivial | rfl,
      by cases g <;> rfl⟩⟩,
    trivial, Or.inl rfl, Or.inr rfl, by decide⟩

theorem loose_not_sufficient : ¬ loose.jointlySufficient .joint := by
  intro h
  have hh : false = true := h false trivial (fun e he => by
    rcases he with he | he
    · rcases he with rfl | rfl <;> trivial
    · exact he.elim)
  exact Bool.noConfusion hh

theorem loose_needed : Needed loose .joint .l .r := by
  constructor
  · refine ⟨Or.inl rfl, fun h => ?_⟩
    have hh : false = true := h false trivial (fun e he => by
      rcases he with ⟨he, _⟩ | he
      · rcases he with rfl | rfl <;> trivial
      · exact he.elim)
    exact Bool.noConfusion hh
  · refine ⟨Or.inr rfl, fun h => ?_⟩
    have hh : false = true := h false trivial (fun e he => by
      rcases he with ⟨he, _⟩ | he
      · rcases he with rfl | rfl <;> trivial
      · exact he.elim)
    exact Bool.noConfusion hh

theorem loose_not_brute : ¬ BruteCoincidence loose .l .r :=
  fun h => h.2.1 fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

/-! The #735 plural fixture. -/
section Plural
open TruthCore.Results.Explanation.UltimateAdequacy

theorem plural_coordinated : Coordinated exercisePlural 0 0 1 :=
  ⟨(background .plural).1, trivial, Or.inl rfl, Or.inr rfl, by decide⟩

theorem plural_sufficient : exercisePlural.jointlySufficient 0 := (background .plural).2.1 0

theorem plural_needed : Needed exercisePlural 0 0 1 := plural_indispensable

theorem plural_source_0 : exercisePlural.exercisedGroups.graph.Source 0 := by
  rintro ⟨y, g, _, (he : g + 2 = 0), _⟩
  omega

theorem plural_source_1 : exercisePlural.exercisedGroups.graph.Source 1 := by
  rintro ⟨y, g, _, (he : g + 2 = 1), _⟩
  omega

theorem plural_brute : BruteCoincidence exercisePlural 0 1 :=
  core _ _ _ _ _ _ _ _ plural_coordinated plural_sufficient plural_source_0 plural_needed

theorem modal_necessary (b : Bool) (e : Nat)
    (h : TruthCore.Explanation.UltimateAdequacy.intrinsic .plural e) :
    NecessaryAt (TruthCore.Explanation.UltimateAdequacy.modal .plural b) false e :=
  fun _ _ => Or.inr (Or.inr h)

theorem narrow_necessary (e : Nat) : NecessaryIn narrow e := by
  rintro _ rfl
  exact actual_occurs .plural e

theorem narrow_coordinated : Coordinated narrow 0 0 1 :=
  ⟨⟨rfl, fun g _ => ⟨trivial, fun e _ => actual_occurs .plural e, actual_occurs .plural (g + 2)⟩⟩,
    trivial, Or.inl rfl, Or.inr rfl, by decide⟩

theorem narrow_sufficient : narrow.jointlySufficient 0 :=
  fun s _ ho => (background .plural).2.1 0 s trivial ho

theorem narrow_fit : MutualFit narrow 0 1 :=
  fun s hs => ⟨fun _ => narrow_necessary 1 s hs, fun _ => narrow_necessary 0 s hs⟩

theorem variation_rival : VariationRival := by
  refine ⟨plural_coordinated, plural_sufficient, plural_needed, plural_brute, plural_source_0,
    plural_source_1, plural_supply, no_least plural_source_0 plural_source_1 (by decide),
    fun b => ⟨modal_necessary b 0 (Or.inl rfl), modal_necessary b 1 (Or.inr rfl), ?_⟩,
    narrow_coordinated, narrow_sufficient, narrow_fit,
    redundant_of_necessary (Or.inl rfl) narrow_sufficient (narrow_necessary 0),
    redundant_of_necessary (Or.inr rfl) narrow_sufficient (narrow_necessary 1),
    narrow_necessary 0, narrow_necessary 1, narrow_necessary 2,
    fun h => h.2.1 narrow_fit, ?_, ?_⟩
  · exact (modal_bridges _ _ _ _ _ _ _ false).2.2 0 0 1 plural_coordinated plural_sufficient
      plural_needed (modal_necessary b 0 (Or.inl rfl))
  · rintro _ rfl
    exact ⟨false, trivial, fun e => ⟨fun _ => Or.inl rfl, fun _ => actual_occurs .plural e⟩⟩
  · intro v _
    exact ⟨(true, true), rfl, fun e => ⟨fun _ => Or.inr (Or.inl rfl), fun _ => actual_occurs .plural e⟩⟩

theorem apart_not_coexist : ¬ Coexist apart 0 1 := by
  rintro ⟨_, h⟩
  exact absurd (show false = true from h) (by decide)

theorem apart_source : apart.exercisedGroups.graph.Source 0 := by
  rintro ⟨y, g, ⟨_, hf⟩, _⟩
  exact hf

theorem ladder : Ladder := by
  refine ⟨⟨⟨fit_actual _, fit_actual _⟩, fun h => h.2.1⟩,
    ⟨⟨(true, true), trivial, actual_occurs .plural 0, actual_occurs .plural 1⟩, apart_not_coexist⟩,
    ⟨loose_coordinated, loose_not_sufficient⟩,
    ⟨(background .branch).1, trivial, Or.inl rfl, Or.inr rfl, by decide⟩,
    (background .branch).2.1 1, branch_no_supply⟩

end Plural

/-! One source: brute remains. -/

theorem single_actual (x : SingleEvent) : single.occurs single.actual x := by
  cases x <;> first | trivial | rfl | exact ⟨rfl, rfl⟩

theorem single_coordinated : Coordinated single .ab .a .b :=
  ⟨⟨trivial, fun _ _ => ⟨trivial, fun e _ => single_actual e, single_actual _⟩⟩,
    trivial, Or.inl rfl, Or.inr rfl, by decide⟩

theorem single_sufficient : single.jointlySufficient .ab := fun _ _ ho =>
  ⟨ho .a (Or.inl (Or.inl rfl)), ho .b (Or.inl (Or.inr rfl))⟩

theorem single_needed : Needed single .ab .a .b := by
  constructor
  · refine ⟨Or.inl rfl, fun h => ?_⟩
    have hh := h (false, true) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · exact (hne he).elim
      · subst he; rfl
      · exact he.elim)
    exact Bool.noConfusion hh.1
  · refine ⟨Or.inr rfl, fun h => ?_⟩
    have hh := h (true, false) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · subst he; rfl
      · exact (hne he).elim
      · exact he.elim)
    exact Bool.noConfusion hh.2

theorem single_source : single.exercisedGroups.graph.Source .r := by
  rintro ⟨y, g, _, he, _⟩
  cases g <;> cases he

theorem single_edge (g : SingleGroup) (y : SingleEvent) (hy : y ∈ single.groups.contributors g) :
    single.exercisedGroups.graph.edge y (single.groups.effect g) :=
  ⟨g, ⟨trivial, trivial⟩, rfl, Or.inl hy⟩

theorem single_not_fit : ¬ MutualFit single .a .b :=
  not_fit (variation single_coordinated single_sufficient single_needed)

theorem single_not_common : ¬ CommonSource single .a .b := by
  rintro ⟨c, _, hca, _, hs, _⟩
  obtain ⟨y, hcy, g, _, he, hy⟩ := Relation.TransGen.tail'_iff.1 hca
  cases g <;> cases he
  rcases hy with hy | hy
  · have hy' : y = .r := hy
    subst hy'
    have hc := refl_source single_source hcy
    subst hc
    have hh : false = true := hs (false, true) trivial (fun e he => by
      rw [Set.mem_singleton_iff.1 he]; trivial)
    exact Bool.noConfusion hh
  · exact hy.elim

theorem single_brute_ctl : SingleSourceBrute := by
  refine ⟨single_coordinated, single_sufficient, single_needed,
    ⟨⟨single_actual _, single_actual _⟩, single_not_fit, single_not_common⟩, ?_, single_source, ?_,
    fun _ _ => trivial, ?_⟩
  · intro x
    have ha : Relation.ReflTransGen single.exercisedGroups.graph.edge .r .a :=
      .single (single_edge .ra .r rfl)
    have hb : Relation.ReflTransGen single.exercisedGroups.graph.edge .r .b :=
      .single (single_edge .rb .r rfl)
    cases x
    · exact .refl
    · exact ha
    · exact hb
    · exact ha.tail (single_edge .ab .a (Or.inl rfl))
  · intro x hx
    cases x
    · rfl
    · exact (hx ⟨_, single_edge .ra .r rfl⟩).elim
    · exact (hx ⟨_, single_edge .rb .r rfl⟩).elim
    · exact (hx ⟨_, single_edge .ab .a (Or.inl rfl)⟩).elim
  · intro x
    have hr : Supply single.groups singleIntrinsic .r := .intrinsic _ rfl
    have ha : Supply single.groups singleIntrinsic .a :=
      Supply.joint (h := single.groups) .ra trivial (fun e (he : e = .r) => he ▸ hr)
    have hb : Supply single.groups singleIntrinsic .b :=
      Supply.joint (h := single.groups) .rb trivial (fun e (he : e = .r) => he ▸ hr)
    have ht : Supply single.groups singleIntrinsic .t :=
      Supply.joint (h := single.groups) .ab trivial (by
        rintro e (rfl | rfl)
        · exact ha
        · exact hb)
    cases x <;> assumption

/-! Guided: common source and needed pair, one or two sources. -/

theorem guided_actual (two : Bool) (x : GuidedEvent) : (guided two).occurs (guided two).actual x := by
  cases x <;> first | trivial | rfl | exact Or.inl rfl | exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem guided_edge (two : Bool) (g : GuidedGroup) (had : g = .lr → two = false) (y : GuidedEvent)
    (hy : y ∈ (guidedGroups two).contributors g) :
    (guided two).exercisedGroups.graph.edge y ((guidedGroups two).effect g) :=
  ⟨g, ⟨had, had⟩, rfl, Or.inl hy⟩

theorem guided_coordinated (two : Bool) : Coordinated (guided two) .ab .a .b :=
  ⟨⟨trivial, fun g hg => ⟨hg, fun e _ => guided_actual two e, guided_actual two _⟩⟩,
    (fun h => by cases h), Or.inl rfl, Or.inr rfl, by decide⟩

theorem guided_sufficient (two : Bool) : (guided two).jointlySufficient .ab := fun _ _ ho =>
  ⟨ho .a (Or.inl (Or.inl rfl)), ho .b (Or.inl (Or.inr rfl))⟩

theorem guided_needed (two : Bool) : Needed (guided two) .ab .a .b := by
  constructor
  · refine ⟨Or.inl rfl, fun h => ?_⟩
    have hh := h (false, false, true) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · exact (hne he).elim
      · subst he; exact Or.inr rfl
      · exact he.elim)
    rcases hh.1 with h1 | h1 <;> exact Bool.noConfusion h1
  · refine ⟨Or.inr rfl, fun h => ?_⟩
    have hh := h (false, true, false) trivial (fun e he => by
      rcases he with ⟨he | he, hne⟩ | he
      · subst he; exact Or.inr rfl
      · exact (hne he).elim
      · exact he.elim)
    rcases hh.2 with h1 | h1 <;> exact Bool.noConfusion h1

theorem guided_common_ab (two : Bool) : CommonSource (guided two) .a .b :=
  ⟨.d, rfl,
    .single (guided_edge two .da (fun h => by cases h) .d rfl),
    .single (guided_edge two .db (fun h => by cases h) .d rfl),
    fun _ _ ho => Or.inl (ho .d rfl), fun _ _ ho => Or.inl (ho .d rfl)⟩

theorem guided_common_ba (two : Bool) : CommonSource (guided two) .b .a := by
  obtain ⟨c, h0, h1, h2, h3, h4⟩ := guided_common_ab two
  exact ⟨c, h0, h2, h1, h4, h3⟩

theorem guided_no_brute (two : Bool) (g : GuidedGroup) (p q : GuidedEvent)
    (hc : Coordinated (guided two) g p q) : ¬ BruteCoincidence (guided two) p q := by
  obtain ⟨_, _, hp, hq, hne⟩ := hc
  intro hb
  cases g
  case ab =>
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact hne rfl
    · exact hb.2.2 (guided_common_ab two)
    · exact hb.2.2 (guided_common_ba two)
    · exact hne rfl
  all_goals exact hne ((show p = _ from hp).trans (show q = _ from hq).symm)

theorem guided_supply (two : Bool) (e : GuidedEvent) :
    Supply (guided two).groups (guidedIntrinsic two) e := by
  have hl : Supply (guidedGroups two) (guidedIntrinsic two) .l := .intrinsic _ (Or.inl rfl)
  have hr : Supply (guidedGroups two) (guidedIntrinsic two) .r := by
    cases two
    · exact Supply.joint (h := guidedGroups false) .lr (fun _ => rfl) (fun e (he : e = .l) => he ▸ hl)
    · exact .intrinsic _ (Or.inr ⟨rfl, rfl⟩)
  have one : ∀ (g : GuidedGroup), g ≠ .lr → ∀ (c : GuidedEvent),
      (guidedGroups two).contributors g = {c} → Supply (guidedGroups two) (guidedIntrinsic two) c →
      Supply (guidedGroups two) (guidedIntrinsic two) ((guidedGroups two).effect g) := by
    intro g hg c hcs hs
    refine Supply.joint g (fun h => (hg h).elim) ?_
    intro e he
    rw [hcs] at he
    rw [Set.mem_singleton_iff.1 he]
    exact hs
  have hd := one .ld (by decide) .l rfl hl
  have hx := one .lx (by decide) .l rfl hl
  have hy := one .ry (by decide) .r rfl hr
  have ha := one .da (by decide) .d rfl hd
  have hb := one .db (by decide) .d rfl hd
  have ht : Supply (guidedGroups two) (guidedIntrinsic two) .t :=
    Supply.joint (h := guidedGroups two) .ab (fun h => by cases h) (by
      rintro e (rfl | rfl)
      · exact ha
      · exact hb)
  cases e
  · exact hl
  · exact hr
  · exact hd
  · exact hx
  · exact hy
  · exact ha
  · exact hb
  · exact ht

theorem guided_source_l (two : Bool) : (guided two).exercisedGroups.graph.Source .l := by
  rintro ⟨y, g, _, he, _⟩
  cases g <;> cases he

theorem guided_source_r : (guided true).exercisedGroups.graph.Source .r := by
  rintro ⟨y, g, ⟨had, _⟩, he, _⟩
  cases g <;> first | exact Bool.noConfusion (had rfl) | cases he

theorem guided_parity : GuidedParity := by
  refine ⟨fun two => ⟨guided_coordinated two, guided_sufficient two, guided_needed two,
      guided_common_ab two, guided_no_brute two, fun _ _ => trivial, fun _ _ => trivial,
      guided_supply two⟩,
    ⟨guided_source_l true, guided_source_r, no_least (guided_source_l true) guided_source_r (by decide)⟩,
    ?_, guided_source_l false, ?_⟩
  all_goals
    have E := guided_edge false
    have ar : ∀ g : GuidedGroup, g = .lr → false = false := fun _ _ => rfl
  · intro z
    have hr : Relation.ReflTransGen (guided false).exercisedGroups.graph.edge .l .r :=
      .single (E .lr (ar _) .l rfl)
    have hd : Relation.ReflTransGen (guided false).exercisedGroups.graph.edge .l .d :=
      .single (E .ld (ar _) .l rfl)
    have hx : Relation.ReflTransGen (guided false).exercisedGroups.graph.edge .l .x :=
      .single (E .lx (ar _) .l rfl)
    have hy := hr.tail (E .ry (ar _) .r rfl)
    have ha := hd.tail (E .da (ar _) .d rfl)
    have hb := hd.tail (E .db (ar _) .d rfl)
    have ht := ha.tail (E .ab (ar _) .a (Or.inl rfl))
    cases z
    · exact .refl
    · exact hr
    · exact hd
    · exact hx
    · exact hy
    · exact ha
    · exact hb
    · exact ht
  · intro z hz
    cases z
    · rfl
    · exact (hz ⟨_, E .lr (ar _) .l rfl⟩).elim
    · exact (hz ⟨_, E .ld (ar _) .l rfl⟩).elim
    · exact (hz ⟨_, E .lx (ar _) .l rfl⟩).elim
    · exact (hz ⟨_, E .ry (ar _) .r rfl⟩).elim
    · exact (hz ⟨_, E .da (ar _) .d rfl⟩).elim
    · exact (hz ⟨_, E .db (ar _) .d rfl⟩).elim
    · exact (hz ⟨_, E .ab (ar _) .a (Or.inl rfl)⟩).elim

theorem core_deletions : CoreDeletions := by
  open TruthCore.Results.Explanation.UltimateAdequacy in
  refine ⟨⟨fun h => h.2.1, fun s hal ho => (background .plural).2.1 0 s hal ho, apart_source,
      plural_indispensable, fun h => apart_not_coexist h.1⟩,
    ⟨loose_coordinated, loose_not_sufficient, fit_source_l, loose_needed, loose_not_brute⟩,
    ⟨guided_coordinated false, guided_sufficient false,
      fun h => h ⟨_, guided_edge false .da (fun _ => rfl) .d rfl⟩,
      guided_needed false, guided_no_brute false _ _ _ (guided_coordinated false)⟩,
    ⟨fit_coordinated, fit_sufficient, fit_source_l, fun h => not_both h.1 fit_redundant_l, fit_not_brute⟩,
    ⟨plural_coordinated, plural_sufficient, plural_source_0, plural_needed, plural_brute⟩⟩

theorem not_source_of_ancestor {A : Type} {K : Graph A} {c x : A} (h : ancestry K c x) :
    ¬ K.Source x := by
  obtain ⟨y, _, hy⟩ := Relation.TransGen.tail'_iff.1 h
  exact fun hs => hs ⟨y, hy⟩

theorem guided_pairwise : PairwiseOrderer (guided true) := by
  intro g p q hc
  obtain ⟨_, _, hp, hq, hne⟩ := hc
  cases g
  case ab =>
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hne rfl).elim
    · obtain ⟨c, _, h1, h2, _⟩ := guided_common_ab true
      exact ⟨c, h1, h2⟩
    · obtain ⟨c, _, h1, h2, _⟩ := guided_common_ba true
      exact ⟨c, h1, h2⟩
    · exact (hne rfl).elim
  all_goals exact (hne ((show p = _ from hp).trans (show q = _ from hq).symm)).elim

theorem single_pairwise : PairwiseOrderer single := by
  intro g p q hc
  obtain ⟨_, _, hp, hq, hne⟩ := hc
  have ha : ancestry single.exercisedGroups.graph .r .a := .single (single_edge .ra .r rfl)
  have hb : ancestry single.exercisedGroups.graph .r .b := .single (single_edge .rb .r rfl)
  cases g
  case ab =>
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨.r, ha, hb⟩
    · exact ⟨.r, hb, ha⟩
    · exact (hne rfl).elim
  all_goals exact (hne ((show p = _ from hp).trans (show q = _ from hq).symm)).elim

theorem order_readings : OrderReadings := by
  refine ⟨fun B E G S m hm g a b hc => ?_, fun B E G S m ⟨c, hc⟩ x y hx hy => ?_,
    ⟨guided_pairwise, ?_, guided_source_l true, guided_source_r⟩,
    ⟨single_pairwise, ⟨.r, single_brute_ctl.2.2.2.2.1⟩, single_brute_ctl.2.2.2.1⟩, ?_, ?_⟩
  · obtain ⟨c, hca, _⟩ := hm g a b hc
    exact not_source_of_ancestor hca
  · exact (refl_source hx (hc x)).symm.trans (refl_source hy (hc y))
  · exact no_least (guided_source_l true) guided_source_r (by decide)
  · intro h
    obtain ⟨c, hca, _⟩ := h _ _ _ fit_coordinated
    exact not_source_of_ancestor hca fit_source_l
  · intro h
    obtain ⟨c, hca, _⟩ := h _ _ _ plural_coordinated
    exact not_source_of_ancestor hca plural_source_0

theorem certificate : TruthCore.Explanation.JointCooperation.Certificate :=
  ⟨coverage, branch_costs, fit_exclusion, core, modal_bridges, ladder, fit_rival, variation_rival,
    single_brute_ctl, guided_parity, core_deletions, order_readings,
    TruthCore.Results.Causality.JointGroups.plural,
    TruthCore.Results.Explanation.UltimateAdequacy.structural⟩

end TruthCore.Results.Explanation.JointCooperation
