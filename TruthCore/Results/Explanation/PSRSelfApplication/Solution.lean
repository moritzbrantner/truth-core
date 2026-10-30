import TruthCore.Explanation.PSRSelfApplication
import TruthCore.Results.Explanation.PSRStrength.Solution

namespace TruthCore.Results.Explanation.PSRSelfApplication
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.PSRSelfApplication
open TruthCore.Logic.SelfApplication

private theorem ff {P : Prop} (h : false = true) : P := Bool.noConfusion h

private theorem nf {P : Prop} {p : Fact} (h : none₀ p = true) : P := by
  cases p <;> exact ff h

/-! ## The scene -/

private theorem contingent_root : Contingent (scene true) .a .root :=
  ⟨rfl, .b, trivial, fun h => ff h⟩

private theorem root_unexplained : ¬ Explained (scene true) .a .root := by
  intro ⟨r, h⟩
  cases r <;> exact ff h

private theorem brute_root : BruteAt (scene true) .a .root :=
  ⟨contingent_root, root_unexplained⟩

private theorem brute_everywhere : ∀ v, ∃ f, BruteAt (scene true) v f := by
  intro v
  cases v
  · exact ⟨.root, brute_root⟩
  · refine ⟨.event, ⟨rfl, .c, trivial, fun h => ff h⟩, ?_⟩
    intro ⟨r, h⟩
    cases r <;> exact ff h
  · refine ⟨.alt, ⟨rfl, .a, trivial, fun h => ff h⟩, ?_⟩
    intro ⟨r, h⟩
    cases r <;> exact ff h

private theorem not_psr (v : Scene) : ¬ ContingentPSR (scene true) v := fun h =>
  match brute_everywhere v with
  | ⟨f, hc, hn⟩ => hn (h f hc)

private theorem not_noBrute : ¬ NoBrute (scene true) .a := fun h => h ⟨.root, brute_root⟩

private theorem event_explained : Explained (scene true) .a .event := ⟨.root, rfl⟩

private theorem factive : Factive (scene true) := by
  intro w r f h
  cases w <;> cases r <;> cases f <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact ff h

private theorem necessitating : Necessitating (scene true) := by
  intro w r f h v _ hr
  cases w <;> cases r <;> cases f <;>
    first
      | exact ff h
      | (cases v <;> first | exact rfl | exact ff hr)

private theorem independent : ReasonIndependent (scene true) := by
  intro w r f h _ hiff
  cases w <;> cases r <;> cases f <;>
    first
      | exact ff h
      | exact ff ((hiff .b trivial).2 rfl)

private theorem irreflexive : IrreflexiveContingent (scene true) := by
  intro w r _ h
  cases w <;> cases r <;> exact ff h

private theorem tracks_psr : TracksPSR (scene true) .psr := fun v =>
  ⟨fun h => by cases v <;> exact ff h, fun h => (not_psr v h).elim⟩

private theorem tracks_rejection : TracksRejection (scene true) .rejection := fun v =>
  ⟨fun _ => brute_everywhere v, fun _ => by cases v <;> rfl⟩

/-! ## Inquiries -/

private theorem edge_at {g : Fact → Fact → Bool} {w : Scene} {e p : Fact}
    (h : (edges g).supports w e p) : g e p = true := h.2

private theorem blank_unsupported (p : Fact) : ¬ Supported blank .a p := by
  intro ⟨e, h⟩
  exact ff h.2

private theorem blank_no_edge : ¬ ∃ e p, blank.supports .a e p := by
  intro ⟨_, _, h⟩
  exact ff h.2

private theorem science_true : EvidenceTrue (scene true) science := by
  intro w e p h
  cases h.1
  cases e <;> cases p <;> first | exact rfl | exact ff h.2

private theorem defense_true : EvidenceTrue (scene true) defense := by
  intro w e p h
  cases h.1
  cases e <;> cases p <;> first | exact rfl | exact ff h.2

private theorem premise_true : EvidenceTrue (scene true) premiseRoot := by
  intro w e p h
  cases h.1
  cases e <;> cases p <;> first | exact rfl | exact ff h.2

private theorem supported_root : Supported science .a .root := ⟨.event, rfl, rfl⟩
private theorem supported_rejection : Supported science .a .rejection := ⟨.event, rfl, rfl⟩

private theorem event_unsupported : ¬ Supported science .a .event := by
  intro ⟨e, h⟩
  cases e <;> exact ff h.2

private theorem science_wf : WellFounded (science.supports .a) := by
  have hevent : Acc (science.supports .a) .event :=
    ⟨_, fun e h => by cases e <;> exact ff h.2⟩
  refine ⟨fun p => ?_⟩
  cases p
  case event => exact hevent
  all_goals
    refine ⟨_, fun e h => ?_⟩
    cases e
    all_goals first | exact hevent | exact ff h.2

private theorem no_descent {α : Type} {r : α → α → Prop} (x : α)
    (step : ∀ y, ∃ z, r z y) : ¬ WellFounded r := fun hwf =>
  hwf.induction (C := fun _ => False) x fun y ih =>
    match step y with
    | ⟨z, h⟩ => ih z h

private theorem loop_not_wf : ¬ WellFounded (loop.supports .a) := fun hwf => by
  have hroot : Acc (loop.supports .a) .root := hwf.apply .root
  have key : ∀ x, Acc (loop.supports .a) x → (x = .root ∨ x = .event) → False := by
    intro x hx
    induction hx with
    | intro y _ ih =>
      intro hy
      cases hy with
      | inl h =>
        subst h
        exact ih .event ⟨rfl, rfl⟩ (Or.inr rfl)
      | inr h =>
        subst h
        exact ih .root ⟨rfl, rfl⟩ (Or.inl rfl)
  exact key .root hroot (Or.inl rfl)

/-! ## Stance facts -/

private theorem critic_core : CoreDemanded critic := by
  intro p h
  cases p <;> first | exact rfl | exact ff h

private theorem noAccept_core : CoreDemanded noAccept := by
  intro p h
  cases p <;> first | exact rfl | exact ff h

private theorem nonCore_core : CoreDemanded nonCore := fun _ h => nf h

private theorem defender_core : CoreDemanded defender := by
  intro p h
  cases p <;> first | exact rfl | exact ff h

private theorem critic_honors : Honors critic science .a := by
  intro p hd ha
  cases p
  case root => exact supported_root
  case rejection => exact supported_rejection
  all_goals first | exact ff hd | exact ff ha

private theorem critic_honors_premise : Honors critic premiseRoot .a := by
  intro p hd ha
  cases p
  case root => exact ⟨.event, rfl, rfl⟩
  case rejection => exact ⟨.root, rfl, rfl⟩
  all_goals first | exact ff hd | exact ff ha

private theorem psr_only_honors (I : Inquiry Scene Fact) : Honors selective I .a := by
  intro p hd ha
  cases p <;> first | exact ff hd | exact ff ha

private theorem nonCore_honors : Honors nonCore blank .a := by
  intro p hd ha
  cases p <;> first | exact ff hd | exact ff ha

private theorem noAccept_honors : Honors noAccept blank .a := fun _ _ ha => nf ha

private theorem critic_not_honors_blank : ¬ Honors critic blank .a := fun h =>
  blank_unsupported .root (h .root rfl rfl)

/-! ## General arguments -/

private theorem core_charge {W F : Type} (S : Stance F) (I : Inquiry W F) (w : W) (b : F)
    (hc : CoreDemanded S) (hh : Honors S I w) (hb : S.core b) (ha : S.accepts b)
    (hn : ¬ Supported I w b) : False :=
  Norm.not_holds_and_acceptable (N := demandNorm S I w) (hc b hb) hn ⟨hh, ha⟩

private theorem regress_core {W F : Type} (S : Stance F) (I : Inquiry W F) (w : W)
    (hb : EveryAcceptedBacked S I w) (hwf : WellFounded (I.supports w))
    (hne : ∃ p, S.accepts p) : False := by
  obtain ⟨p, hp⟩ := hne
  have key : S.accepts p → False :=
    hwf.induction (C := fun x => S.accepts x → False) p fun x ih hx =>
      match hb x hx with
      | ⟨e, he, hs⟩ => ih e hs he
  exact key hp

theorem stanceMap : StanceMap := by
  refine ⟨fun _ _ p h => h p, ⟨fun _ h => nf h, fun h => nf h, rfl, fun h => h .psr rfl⟩,
    fun _ _ S I w b => core_charge S I w b,
    ⟨fun h => ff (h .root rfl), psr_only_honors _, rfl, rfl, blank_unsupported _⟩,
    ⟨critic_core, critic_not_honors_blank, rfl, rfl, blank_unsupported _⟩,
    ⟨nonCore_core, nonCore_honors, fun h => ff h, rfl, blank_unsupported _⟩,
    ⟨noAccept_core, noAccept_honors, rfl, fun h => ff h, blank_unsupported _⟩,
    ⟨critic_core, critic_honors, rfl, rfl, supported_root⟩,
    fun _ _ S I w _ hd hn => Norm.selfApplication (N := demandNorm S I w) hd hn,
    ?_, ?_, ?_, ?_,
    fun _ _ _ _ _ _ h _ => h, fun _ d => ⟨d, fun _ _ h => h⟩, ?_,
    fun _ _ S I w => regress_core S I w,
    ⟨fun h => event_unsupported (match h .event rfl with | ⟨e, _, hs⟩ => ⟨e, hs⟩),
      science_wf, rfl⟩,
    ⟨?_, loop_not_wf, rfl, ?_⟩,
    ⟨fun p _ => ⟨p + 1, trivial, rfl⟩,
      no_descent 0 fun y => ⟨y + 1, rfl⟩, trivial,
      fun e p h => by cases h; exact Nat.lt_succ_self p⟩,
    ⟨fun _ h => nf h, science_wf, fun _ h => nf h⟩,
    ⟨defender_core, ?_, rfl, ⟨.event, rfl, rfl⟩, defense_true, fun h => ff h, not_psr _⟩⟩
  · intro _ S k target own hown hk ht
    cases hown with
    | inl h => exact Or.inl ⟨ht, h⟩
    | inr h =>
      cases hk with
      | inl hk => exact Or.inr (Or.inl ⟨ht, h, hk⟩)
      | inr hk => exact Or.inr (Or.inr ⟨ht, h, hk⟩)
  · intro _ S k target own
    exact ⟨fun ⟨u, s⟩ => s.2.1 u.2, fun ⟨u, r⟩ => r.2.1 u.2, fun ⟨s, r⟩ => r.2.2 s.2.2⟩
  · exact ⟨factive, necessitating, independent, irreflexive, science_true, tracks_psr,
      tracks_rejection, critic_core, critic_honors, rfl, fun h => ff h, rfl, rfl, brute_root,
      not_noBrute, supported_root, supported_rejection, event_explained, event_unsupported,
      rfl, ⟨rfl, rfl⟩, fun h => ff h, fun h => ff h.2⟩
  · refine ⟨psr_only_honors _, ⟨rfl, fun h => ff h, ?_⟩, ⟨rfl, fun h => ff h, ?_⟩, rfl⟩
    · exact ⟨fun _ => trivial, fun _ => trivial⟩
    · exact fun h => (h.1 trivial).elim
  · refine ⟨fun _ h _ => h, ?_, ?_, ?_⟩
    · intro h
      obtain ⟨r, hr⟩ := h .event rfl ⟨rfl, .c, trivial, fun h => ff h⟩
      cases r <;> exact ff hr
    · intro f hf _
      cases hf
      exact event_explained
    · exact fun h => root_unexplained (h .root rfl contingent_root)
  · intro p hp
    cases p
    case root => exact ⟨.event, rfl, ⟨rfl, rfl⟩⟩
    case event => exact ⟨.root, rfl, ⟨rfl, rfl⟩⟩
    all_goals exact ff hp
  · intro e h
    cases e <;> exact ff h.2
  · intro p hd ha
    cases p
    case psr => exact ⟨.event, rfl, rfl⟩
    all_goals first | exact ff hd | exact ff ha

private theorem ground_noBrute (v : Bool) : NoBrute (ground true) v := by
  intro ⟨f, ⟨hf, u, _, hu⟩, hne⟩
  cases f with
  | ground => exact hu trivial
  | choice =>
    cases v with
    | false => exact hne ⟨.ground, rfl⟩
    | true => exact Bool.noConfusion hf

private theorem ground_false_unexplained : ¬ Explained (ground false) false .ground := by
  intro ⟨r, h⟩
  cases r with
  | ground => exact Bool.noConfusion h
  | choice => exact h

theorem bridgeLadder : BridgeLadder := by
  refine ⟨fun _ _ _ _ _ D b hb hr hd => hb.2 (hr b hd hb.1),
    fun _ _ _ _ _ _ b hr hd f hf hc => by cases hf; exact hr _ hd hc,
    fun _ _ _ _ _ _ b ht hb hs => hb.2 (ht b hb.1 hs),
    fun _ _ _ _ _ _ h f hc _ => h f hc,
    fun _ _ _ _ _ _ hcov ht f hc => ht f hc (hcov f hc),
    ⟨fun f _ hs => (blank_unsupported f hs).elim, not_psr _,
      fun h => root_unexplained (h .root contingent_root supported_root)⟩,
    fun _ _ _ _ _ _ h e _ _ hc => h e hc,
    fun _ _ _ _ _ _ b p he hb hs => hb.2 (he b p hs hb.1),
    ⟨?_, brute_root, supported_root, not_psr _⟩,
    ⟨critic_core, critic_honors_premise, premise_true, ⟨rfl, rfl⟩,
      fun h => root_unexplained (h .root .rejection ⟨rfl, rfl⟩ contingent_root)⟩,
    fun _ _ _ _ _ _ e p hg hs v hv ⟨f, hb⟩ => hg ⟨v, f, hv, hb⟩ ⟨e, p, hs⟩,
    ?_,
    ⟨fun h => h ⟨.a, .root, trivial, brute_root⟩ ⟨.event, .root, rfl, rfl⟩,
      brute_root, ⟨rfl, rfl⟩⟩,
    ⟨fun ⟨v, f, _, hb⟩ => (ground_noBrute v ⟨f, hb⟩).elim, ⟨rfl, rfl⟩, ground_noBrute,
      ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩⟩,
    ⟨fun _ h => (blank_no_edge h).elim, brute_root, blank_no_edge⟩,
    ?_, ?_,
    ⟨?_, ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩, rfl, fun _ => trivial⟩,
    ⟨?_, fun _ => trivial, ground_false_unexplained,
      fun h => ground_false_unexplained (h .ground trivial),
      fun h => root_unexplained (h .root rfl)⟩⟩
  · intro e p h hc
    cases h.1
    cases e <;> cases p <;>
      first
        | exact event_explained
        | exact ff h.2
  · intro _ _ _ _ I S w v f c hg hv hb hd ha hh
    obtain ⟨e, he⟩ := hh c hd ha
    exact hg ⟨v, f, hv, hb⟩ ⟨e, c, he⟩
  · intro _ _ _ A I a e p t c hg hs hr hsound hfac hnec hdis hirr ht hc
    exact TruthCore.Results.Explanation.PSRStrength.collapse_distribution A a t c
      hsound hfac hnec hdis hirr ht hc
      (fun hb => match hb with
        | ⟨f, hb'⟩ => hg ⟨a, f, hr, hb'⟩ ⟨e, p, hs⟩)
  · intro _ _ _ A w r f hn hr he hc
    obtain ⟨_, v, hv, hf⟩ := hc
    exact hf (hn w r f he v hv (hr v hv))
  · intro h
    exact Bool.noConfusion (h false .ground .choice rfl true trivial trivial)
  · exact TruthCore.Results.Explanation.PSRStrength.strengthMap.2.2.2.1.2.2.1 false

end TruthCore.Results.Explanation.PSRSelfApplication
