import TruthCore.Explanation.StoppingPoints
import TruthCore.Results.Explanation.PSRStrength.Solution

namespace TruthCore.Results.Explanation.StoppingPoints
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.PSRSelfApplication
open TruthCore.Explanation.StoppingPoints
open TruthCore.Results.Explanation.PSRStrength

variable {W B F : Type}

/-! ## General lemmas -/

theorem core_necessitating (A : Arena W B F) (a : W) (c : F) (hc : Contingent A a c)
    (hb : NoBrute A a) (hf : Factive A) (hn : Necessitating A)
    (hwf : WellFounded (A.explains a)) : False :=
  hwf.induction (C := fun f => Contingent A a f → False) c
    (fun f ih hcf => hb ⟨f, hcf, fun ⟨r, he⟩ =>
      ih r he (necessitating_reason_contingent A hn he (hf a r f he).1 hcf)⟩) hc

theorem core_unrestricted (A : Arena W B F) (a : W) (t : F) (ht : A.holds a t)
    (hp : FactPSR A a) (hf : Factive A) (hwf : WellFounded (A.explains a)) : False :=
  hwf.induction (C := fun f => A.holds a f → False) t
    (fun f ih hh => by
      obtain ⟨r, he⟩ := hp f hh
      exact ih r he (hf a r f he).1) ht

theorem work_contingent (A : Arena W B F) (w : W) (s t : F) (hf : Factive A)
    (he : A.explains w s t) (hc : Contingent A w t) (hw : WorkNecessitates A w s) :
    Contingent A w s := by
  obtain ⟨_, v, hv, hn⟩ := hc
  exact ⟨(hf w s t he).1, v, hv, fun h => hn (hw t he v hv h)⟩

theorem terminal_brute (A : Arena W B F) (w : W) (s t : F) (hf : Factive A)
    (hi : IrreflexiveContingent A) (ht : Terminal A w s) (he : A.explains w s t)
    (hc : Contingent A w t) (hw : WorkNecessitates A w s) : BruteAt A w s := by
  have hs := work_contingent A w s t hf he hc hw
  refine ⟨hs, fun ⟨r, hr⟩ => ?_⟩
  have := ht.2 r hr
  subst this
  exact hi w r hs hr

theorem stop_fork (A : Arena W B F) (w : W) (s t : F) (hf : Factive A)
    (ht : Terminal A w s) (he : A.explains w s t) (hc : Contingent A w t)
    (dc : Contingent A w s ∨ ¬ Contingent A w s) (de : Explained A w s ∨ ¬ Explained A w s) :
    BruteAt A w s ∨ (Contingent A w s ∧ A.explains w s s) ∨
      (¬ Contingent A w s ∧ ¬ WorkNecessitates A w s) := by
  cases dc with
  | inr h => exact .inr (.inr ⟨h, fun hw => h (work_contingent A w s t hf he hc hw)⟩)
  | inl h =>
    cases de with
    | inr hn => exact .inl ⟨h, hn⟩
    | inl hx =>
      obtain ⟨r, hr⟩ := hx
      have := ht.2 r hr
      subst this
      exact .inr (.inl ⟨h, hr⟩)

private theorem supplied_back (A : Arena W B F) (w : W) {r f x : F}
    (he : A.explains w r f) (h : Supplied A w (· = f) x) : Supplied A w (· = r) x := by
  induction h with
  | base hs =>
    subst hs
    exact .step he (.base rfl)
  | step hx _ ih => exact .step hx ih

private theorem supplied_pick (A : Arena W B F) (w : W) {S : F → Prop} {t : F}
    (h : Supplied A w S t) : ∃ x, S x ∧ Supplied A w (· = x) t := by
  induction h with
  | @base f hs => exact ⟨f, hs, .base rfl⟩
  | step he _ ih =>
    obtain ⟨x, hx, hp⟩ := ih
    exact ⟨x, hx, .step he hp⟩

private theorem strict_supplied (A : Arena W B F) (w : W) {s t : F}
    (h : Strict A w s t) : Supplied A w (· = s) t := by
  obtain ⟨r, he, hs⟩ := h
  exact .step he hs

theorem norm_implication (A : Arena W B F) (a : W) (t : F) (hc : Contingent A a t)
    (hx : Explained A a t) (hs : SingleStop A a t) (hf : Factive A) (hn : Necessitating A)
    (hwf : WellFounded (A.explains a)) (hnorm : NoBruteFoundation A a) : False := by
  obtain ⟨r₀, he₀⟩ := hx
  have hdown : ∀ f, Contingent A a f → Strict A a f t → False := fun f =>
    hwf.induction (C := fun f => Contingent A a f → Strict A a f t → False) f
      (fun f ih hcf hst => by
        have hne : ¬ Explained A a f := fun ⟨r, he⟩ => by
          apply ih r he (necessitating_reason_contingent A hn he (hf a r f he).1 hcf)
          obtain ⟨q, hq, hsup⟩ := hst
          exact ⟨q, hq, supplied_back A a he hsup⟩
        have hterm : Terminal A a f := ⟨hcf.1, fun r hr => (hne ⟨r, hr⟩).elim⟩
        refine hnorm f t ⟨hterm, hst, fun hsup => ?_⟩ ⟨hcf, hne⟩
        obtain ⟨x, ⟨hxt, hxn⟩, hp⟩ := supplied_pick A a hsup
        exact hxn (hs x f hxt hterm hp (strict_supplied A a hst)))
  exact hdown r₀ (necessitating_reason_contingent A hn he₀ (hf a r₀ t he₀).1 hc)
    ⟨r₀, he₀, .base rfl⟩

theorem wf_rank {α : Type} {R : α → α → Prop} (rank : α → Nat)
    (h : ∀ r f, R r f → rank r < rank f) : WellFounded R :=
  Subrelation.wf (fun {a b} hr => h a b hr) (InvImage.wf rank Nat.lt_wfRel.wf)

private theorem ff {P : Prop} (h : false = true) : P := Bool.noConfusion h

/-! ## Reused witnesses -/

private theorem bt_factive : Factive bruteTerminus := collapseCore.2.2.1.2.1
private theorem bt_nec : Necessitating bruteTerminus := collapseCore.2.2.1.2.2.1
private theorem bt_notbrute : ¬ NoBrute bruteTerminus false :=
  collapseCore.2.2.1.2.2.2.2.2.2.2
private theorem ft_notfactive : ¬ Factive falseToken := collapseCore.2.2.2.1.2.1
private theorem ft_nec : Necessitating falseToken := collapseCore.2.2.2.1.2.2.1
private theorem ft_cont : Contingent falseToken false true :=
  collapseCore.2.2.2.1.2.2.2.2.2.2.1
private theorem ft_nobrute : NoBrute falseToken false :=
  collapseCore.2.2.2.1.2.2.2.2.2.2.2
private theorem cf_factive : Factive cofinite := collapseCore.2.2.2.2.2.1.2.1
private theorem cf_nec : Necessitating cofinite := collapseCore.2.2.2.2.2.1.2.2.1
private theorem cf_no_bccf : ∀ a t, ¬ BCCFAt cofinite a t :=
  collapseCore.2.2.2.2.2.1.2.2.2.2.2.1
private theorem cf_some_contingent : ∀ a, ∃ c, Contingent cofinite a c :=
  collapseCore.2.2.2.2.2.1.2.2.2.2.2.2.1
private theorem cf_nobrute : ∀ a, NoBrute cofinite a :=
  collapseCore.2.2.2.2.2.1.2.2.2.2.2.2.2
private theorem mr_factive : Factive mutualReasons := collapseCore.2.2.2.2.2.2.1.2.1
private theorem mr_nec : Necessitating mutualReasons := collapseCore.2.2.2.2.2.2.1.2.2.1
private theorem mr_cont : Contingent mutualReasons false true :=
  collapseCore.2.2.2.2.2.2.1.2.2.2.2.2.2.1
private theorem mr_nobrute : NoBrute mutualReasons false :=
  collapseCore.2.2.2.2.2.2.1.2.2.2.2.2.2.2

private theorem cf_factPSR (a : Nat) : FactPSR cofinite a :=
  (strengthMap.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1) a

private theorem cf_not_wf (a : Nat) : ¬ WellFounded (cofinite.explains a) :=
  core_unrestricted cofinite a [] (fun h => nomatch h) (cf_factPSR a) cf_factive

private theorem cf_no_terminal (a : Nat) (s : List Nat) : ¬ Terminal cofinite a s := by
  intro ⟨hs, ht⟩
  obtain ⟨r, he⟩ := cf_factPSR a s hs
  have := ht r he
  subst this
  obtain ⟨_, _, x, hx, hnx⟩ := he
  exact hnx hx

/-! ## The ground -/

private theorem g_factive (b : Bool) : Factive (ground b) := by
  intro w r f h
  cases r <;> cases f <;> cases w <;>
    first
    | exact ⟨trivial, rfl⟩
    | exact ⟨trivial, trivial⟩
    | exact False.elim h
    | exact Bool.noConfusion h

private theorem g_terminal (b : Bool) : Terminal (ground b) false .ground := by
  refine ⟨trivial, fun r h => ?_⟩
  cases r
  · rfl
  · exact False.elim h

private theorem g_not_contingent (b : Bool) (w : Bool) :
    ¬ Contingent (ground b) w .ground := fun ⟨_, _, _, h⟩ => h trivial

private theorem g_choice (b : Bool) : Contingent (ground b) false .choice :=
  ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩

private theorem g_work (b : Bool) : ¬ WorkNecessitates (ground b) false .ground :=
  fun h => Bool.noConfusion (h .choice rfl true trivial trivial)

private theorem g_explains (b : Bool) : (ground b).explains false .ground .choice := rfl

private theorem g_no_self : ¬ Explained (ground false) false .ground := by
  intro ⟨r, h⟩
  cases r
  · exact Bool.noConfusion h
  · exact False.elim h

private theorem g_nobrute (b : Bool) : ∀ s, ¬ BruteAt (ground b) false s := by
  intro s h
  cases s
  · exact g_not_contingent b false h.1
  · exact h.2 ⟨.ground, rfl⟩

private theorem gf_wf : WellFounded ((ground false).explains false) :=
  wf_rank (fun f => match f with | .ground => 0 | .choice => 1) (by
    intro r f h
    cases r <;> cases f
    · exact Bool.noConfusion h
    · exact Nat.zero_lt_one
    · exact False.elim h
    · exact False.elim h)

private theorem gf_not_nec : ¬ Necessitating (ground false) :=
  fun h => g_work false fun t he v hv hs => h false .ground t he v hv hs

private theorem gf_nobrute : NoBrute (ground false) false :=
  fun ⟨s, hb⟩ => g_nobrute false s hb

private theorem gf_choice_terminal_absurd : ¬ Terminal (ground false) false .choice :=
  fun h => GroundFact.noConfusion (h.2 .ground rfl)

private theorem gf_foundation : Foundation (ground false) false .ground .choice := by
  refine ⟨g_terminal false, ⟨.ground, rfl, .base rfl⟩, fun h => ?_⟩
  cases h with
  | base hs => exact gf_choice_terminal_absurd hs.1
  | @step r _ he hs =>
    cases r with
    | choice => exact False.elim he
    | ground =>
      cases hs with
      | base hb => exact hb.2 rfl
      | @step q _ he' _ =>
        cases q
        · exact Bool.noConfusion he'
        · exact False.elim he'

private theorem gf_single : SingleStop (ground false) false .choice := by
  intro x y hx hy _ _
  cases x
  · cases y
    · rfl
    · exact (gf_choice_terminal_absurd hy).elim
  · exact (gf_choice_terminal_absurd hx).elim

/-! ## The other models -/

private theorem bt_terminal : Terminal bruteTerminus false .terminus := by
  refine ⟨rfl, fun r h => ?_⟩
  cases r <;> exact False.elim h

private theorem bt_not_explained : ¬ Explained bruteTerminus false .terminus := by
  intro ⟨r, h⟩
  cases r <;> exact False.elim h

private theorem bt_contingent (f : TerminusFact) : Contingent bruteTerminus false f :=
  ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩

private theorem bt_wf : WellFounded (bruteTerminus.explains false) :=
  wf_rank (fun f => match f with | .terminus => 0 | .effect => 1 | .whole => 0) (by
    intro r f h
    cases r <;> cases f <;> first | exact Nat.zero_lt_one | exact False.elim h)

private theorem bt_work : WorkNecessitates bruteTerminus false .terminus :=
  fun t he v hv hs => bt_nec false .terminus t he v hv hs

private theorem bt_effect_not_terminal : ¬ Terminal bruteTerminus false .effect :=
  fun h => TerminusFact.noConfusion (h.2 .terminus rfl)

private theorem bt_supplied_effect {S : TerminusFact → Prop}
    (h : Supplied bruteTerminus false S .effect) : S .effect ∨ S .terminus := by
  cases h with
  | base hs => exact .inl hs
  | @step r _ he hs =>
    cases r with
    | effect => exact False.elim he
    | whole => exact False.elim he
    | terminus =>
      cases hs with
      | base hb => exact .inr hb
      | @step q _ he' _ => cases q <;> exact False.elim he'

private theorem bt_foundation : Foundation bruteTerminus false .terminus .effect := by
  refine ⟨bt_terminal, ⟨.terminus, rfl, .base rfl⟩, fun h => ?_⟩
  cases bt_supplied_effect h with
  | inl hs => exact bt_effect_not_terminal hs.1
  | inr hs => exact hs.2 rfl

private theorem bt_single : SingleStop bruteTerminus false .effect := by
  intro x y hx hy sx sy
  have key : ∀ z, Terminal bruteTerminus false z →
      Supplied bruteTerminus false (· = z) .effect → z = .terminus := by
    intro z hz hs
    cases bt_supplied_effect hs with
    | inl h =>
      subst h
      exact (bt_effect_not_terminal hz).elim
    | inr h => exact h.symm
  rw [key x hx sx, key y hy sy]

private theorem ns_not_contingent (w : Bool) (c : Bool) : ¬ Contingent necessaryStop w c :=
  fun ⟨_, _, _, h⟩ => h trivial

private theorem ns_wf : WellFounded (necessaryStop.explains false) :=
  wf_rank (fun b => if b then 1 else 0) (by
    intro r f h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact Nat.zero_lt_one)

private theorem ns_factive : Factive necessaryStop := fun _ _ _ _ => ⟨trivial, trivial⟩

private theorem ns_nec : Necessitating necessaryStop := fun _ _ _ _ _ _ _ => trivial

private theorem ns_terminal : Terminal necessaryStop false false :=
  ⟨trivial, fun _ h => Bool.noConfusion h.2⟩

private theorem ns_not_explained : ¬ Explained necessaryStop false false :=
  fun ⟨_, h⟩ => Bool.noConfusion h.2

private theorem ns_nobrute : NoBruteFoundation necessaryStop false :=
  fun s _ _ hb => ns_not_contingent false s hb.1

private theorem ns_single : SingleStop necessaryStop false true := by
  have key : ∀ z, Terminal necessaryStop false z → z = false := by
    intro z hz
    cases z
    · rfl
    · exact (hz.2 false ⟨rfl, rfl⟩).symm
  intro x y hx hy _ _
  rw [key x hx, key y hy]

private theorem ft_wf : WellFounded (falseToken.explains false) :=
  wf_rank (fun b => if b then 1 else 0) (by
    intro r f h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact Nat.zero_lt_one)

private theorem ft_no_terminal : ∀ z, ¬ Terminal falseToken false z := by
  intro z hz
  cases z
  · exact Bool.noConfusion hz.1.1
  · exact Bool.noConfusion (hz.2 false ⟨rfl, rfl⟩)

private theorem ft_explained : Explained falseToken false true := ⟨false, rfl, rfl⟩

private theorem mr_not_wf : ¬ WellFounded (mutualReasons.explains false) := by
  intro hwf
  have hc : ∀ f, mutualReasons.holds false f → False := fun f =>
    hwf.induction (C := fun f => mutualReasons.holds false f → False) f
      (fun f ih _ => by
        cases f
        · exact ih true ⟨rfl, Bool.noConfusion⟩ rfl
        · exact ih false ⟨rfl, Bool.noConfusion⟩ rfl)
  exact hc false rfl

/-! ## `isolated`, `noTruth`, `selfWork` -/

private theorem is_cont : Contingent isolated false () :=
  ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩
private theorem is_ne : ¬ Explained isolated false () := fun ⟨_, h⟩ => h
private theorem is_factive : Factive isolated := fun _ _ _ h => h.elim
private theorem is_nec : Necessitating isolated := fun _ _ _ h => h.elim
private theorem is_wf : WellFounded (isolated.explains false) :=
  wf_rank (fun _ => 0) (fun _ _ h => h.elim)
private theorem is_norm : NoBruteFoundation isolated false :=
  fun _ _ h _ => by
    obtain ⟨_, ⟨_, he, _⟩, _⟩ := h
    exact he

private theorem nt_wf : WellFounded (noTruth.explains ()) :=
  wf_rank (fun _ => 0) (fun _ _ h => h.elim)

private theorem sw_factive : Factive selfWork := fun _ _ _ h => ⟨h.1, h.1⟩

/-! ## Twin roots -/

private theorem tw_nec : Necessitating twinRoots := fun _ _ _ _ _ _ h => h

private theorem tw_factive : Factive twinRoots := by
  intro w r f h
  cases r <;> cases f <;>
    first
    | exact False.elim h
    | exact ⟨h, h⟩

private theorem tw_wf : WellFounded (twinRoots.explains false) :=
  wf_rank (fun f => match f with | .left => 0 | .right => 0 | .effect => 1) (by
    intro r f h
    cases r <;> cases f <;> first | exact Nat.zero_lt_one | exact False.elim h)

private theorem tw_terminal_left : Terminal twinRoots false .left := by
  refine ⟨rfl, fun r h => ?_⟩
  cases r <;> exact False.elim h

private theorem tw_terminal_right : Terminal twinRoots false .right := by
  refine ⟨rfl, fun r h => ?_⟩
  cases r <;> exact False.elim h

private theorem tw_ne_left : ¬ Explained twinRoots false .left := by
  intro ⟨r, h⟩
  cases r <;> exact False.elim h

private theorem tw_ne_right : ¬ Explained twinRoots false .right := by
  intro ⟨r, h⟩
  cases r <;> exact False.elim h

private theorem tw_cont (f : TwinFact) : Contingent twinRoots false f :=
  ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩

private theorem tw_left : twinRoots.explains false .left .effect := rfl
private theorem tw_right : twinRoots.explains false .right .effect := rfl

private theorem tw_norm : NoBruteFoundation twinRoots false := by
  intro s t hF hB
  obtain ⟨_, ⟨r, he, _⟩, hno⟩ := hF
  cases s with
  | effect => exact hB.2 ⟨.left, rfl⟩
  | left =>
    cases t with
    | effect =>
      exact hno (.step tw_right (.base ⟨tw_terminal_right, TwinFact.noConfusion⟩))
    | left => cases r <;> exact False.elim he
    | right => cases r <;> exact False.elim he
  | right =>
    cases t with
    | effect =>
      exact hno (.step tw_left (.base ⟨tw_terminal_left, TwinFact.noConfusion⟩))
    | left => cases r <;> exact False.elim he
    | right => cases r <;> exact False.elim he

private theorem tw_not_single : ¬ SingleStop twinRoots false .effect := fun h =>
  TwinFact.noConfusion (h .left .right tw_terminal_left tw_terminal_right
    (.step tw_left (.base rfl)) (.step tw_right (.base rfl)))

/-! ## The contingent law and the unexplained whole -/

private theorem law_terminal : Terminal (history true) .lawful .law := by
  refine ⟨trivial, fun r h => ?_⟩
  cases r <;> exact False.elim h.2

private theorem law_ne : ¬ Explained (history true) .lawful .law := by
  intro ⟨r, h⟩
  cases r <;> exact False.elim h.2

private theorem law_cont : Contingent (history true) .lawful .law :=
  ⟨trivial, .rogue, trivial, id⟩

private theorem law_work : WorkNecessitates (history true) .lawful .law := by
  intro t he v _ hv
  cases v with
  | rogue => exact False.elim hv
  | cut k => exact False.elim hv
  | lawful => cases t <;> exact trivial

private theorem law_indep : WorkIndependent (history true) .lawful .law := by
  intro t he h
  cases t with
  | law => exact False.elim he.2
  | hist => exact (h .rogue trivial).2 trivial
  | member n => exact (h .rogue trivial).2 trivial

private theorem hist_not_terminal_of_reason : ¬ Terminal (history true) .lawful .hist :=
  fun h => HistoryFact.noConfusion (h.2 .law ⟨rfl, rfl⟩)

private theorem law_foundation : Foundation (history true) .lawful .law .hist := by
  refine ⟨law_terminal, ⟨.law, ⟨rfl, rfl⟩, .base rfl⟩, fun h => ?_⟩
  cases h with
  | base hs => exact hist_not_terminal_of_reason hs.1
  | @step r _ he hs =>
    cases r with
    | member n => exact False.elim he.2
    | hist => exact False.elim he.2
    | law =>
      cases hs with
      | base hb => exact hb.2 rfl
      | @step q _ he' _ => cases q <;> exact False.elim he'.2

private theorem hist_terminal : Terminal (history false) .lawful .hist := by
  refine ⟨trivial, fun r h => ?_⟩
  cases r with
  | member n => exact False.elim h.2
  | hist => rfl
  | law => exact Bool.noConfusion h.2

private theorem hist_ne : ¬ Explained (history false) .lawful .hist := by
  intro ⟨r, h⟩
  cases r with
  | member n => exact False.elim h.2
  | hist => exact False.elim h.2
  | law => exact Bool.noConfusion h.2

private theorem hist_cont : Contingent (history false) .lawful .hist :=
  ⟨trivial, .cut 0, trivial, id⟩

private theorem hist_no_work (t : HistoryFact) : ¬ (history false).explains .lawful .hist t := by
  intro h
  cases t <;> exact False.elim h.2

/-! ## The scene -/

private theorem scene_terminal : Terminal (scene true) .a .root := by
  refine ⟨rfl, fun r h => ?_⟩
  cases r <;> exact ff h

private theorem scene_brute : BruteAt (scene true) .a .root := by
  refine ⟨⟨rfl, .b, trivial, fun h => ff h⟩, fun ⟨r, h⟩ => ?_⟩
  cases r <;> exact ff h

private theorem scene_foundation : Foundation (scene true) .a .root .event := by
  refine ⟨scene_terminal, ⟨.root, rfl, .base rfl⟩, fun h => ?_⟩
  cases h with
  | base hs => exact Fact.noConfusion (hs.1.2 .root rfl)
  | @step r _ he hs =>
    cases r with
    | root =>
      cases hs with
      | base hb => exact hb.2 rfl
      | @step q _ he' _ => cases q <;> exact ff he'
    | event => exact ff he
    | alt => exact ff he
    | psr => exact ff he
    | rejection => exact ff he

private theorem blank_unsupported : ¬ Supported blank .a .root := by
  intro ⟨e, _, h⟩
  exact ff h

/-! ## `rivalStops` -/

private theorem rs_terminal_brute : Terminal rivalStops false .brute := by
  refine ⟨rfl, fun r h => ?_⟩
  cases r <;> exact False.elim h

private theorem rs_terminal_nature : Terminal rivalStops false .nature := by
  refine ⟨trivial, fun r h => ?_⟩
  cases r <;> exact False.elim h

/-! ## Certificates -/

theorem stoppingMap : StoppingMap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ A a c hc hb hf hn hwf => core_necessitating A a c hc hb hf hn hwf
  · exact ⟨bt_notbrute, bt_contingent _, bt_factive, bt_nec, bt_wf⟩
  · exact ⟨ns_not_contingent, fun ⟨s, h, _⟩ => ns_not_contingent false s h, ns_factive, ns_nec, ns_wf⟩
  · exact ⟨ft_notfactive, ft_cont, ft_nobrute, ft_nec, ft_wf⟩
  · exact ⟨gf_not_nec, g_choice false, gf_nobrute, g_factive false, gf_wf⟩
  · exact fun a => ⟨cf_not_wf a, cf_some_contingent a, cf_nobrute a, cf_factive, cf_nec⟩
  · exact ⟨mr_not_wf, mr_cont, mr_nobrute, mr_factive, mr_nec⟩
  · exact fun _ _ _ A a t ht hp hf hwf => core_unrestricted A a t ht hp hf hwf
  · refine ⟨fun h => g_no_self (h .ground trivial), trivial, g_factive false, gf_wf⟩
  · refine ⟨fun hwf => ?_, trivial, ?_, g_factive true⟩
    · have hc : ∀ f, (f = GroundFact.ground) → False := fun f =>
        hwf.induction (C := fun f => f = GroundFact.ground → False) f
          (fun f ih hf => ih .ground (by subst hf; rfl) rfl)
      exact hc .ground rfl
    · intro f _
      cases f
      · exact ⟨.ground, rfl⟩
      · exact ⟨.ground, rfl⟩
  · exact ⟨ft_notfactive, ⟨rfl, rfl⟩, by
      intro f hf
      cases f
      · exact Bool.noConfusion hf.1
      · exact ft_explained, ft_wf⟩
  · exact ⟨fun _ h => h, fun _ h => h.elim, fun _ _ _ h => h.elim, nt_wf⟩
  · exact fun _ _ _ A w s t hf he hc hw => work_contingent A w s t hf he hc hw
  · exact fun _ _ _ A w s t hf hi ht he hc hw => terminal_brute A w s t hf hi ht he hc hw
  · exact fun _ _ _ A w s t hf ht he hc dc de => stop_fork A w s t hf ht he hc dc de
  · intro _ _ _ A w s
    exact ⟨fun ⟨h, _, hs⟩ => h.2 ⟨s, hs⟩, fun ⟨h, hn, _⟩ => hn h.1,
      fun ⟨⟨h, _⟩, hn, _⟩ => hn h⟩
  · exact ⟨⟨bt_contingent _, bt_not_explained⟩, bt_terminal, rfl, bt_contingent _⟩
  · refine ⟨⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩, ⟨rfl, rfl⟩, ?_, ⟨rfl, rfl⟩,
      ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩, sw_factive⟩
    refine ⟨rfl, fun r h => h.2⟩
  · exact ⟨g_not_contingent true false, g_work true, g_terminal true, g_explains true, g_choice true⟩
  · exact ⟨bt_terminal, bt_not_explained, bt_contingent _, bt_work,
      fun h => h .effect rfl (fun _ _ => Iff.rfl)⟩
  · exact ⟨g_terminal true, ⟨.ground, rfl⟩, g_not_contingent true false, g_work true,
      fun h => h .ground rfl (fun _ _ => Iff.rfl)⟩
  · refine ⟨g_terminal false, g_no_self, g_not_contingent false false, g_work false, ?_⟩
    intro t he h
    cases t
    · exact Bool.noConfusion he
    · exact Bool.noConfusion ((h true trivial).1 trivial)
  · exact ⟨law_terminal, law_ne, law_cont, law_work, law_indep⟩
  · exact ⟨hist_terminal, hist_ne, hist_cont, hist_no_work⟩
  · exact ⟨ns_terminal, ns_not_explained, ns_not_contingent false false,
      fun _ _ _ _ _ => trivial,
      fun h => h true ⟨rfl, rfl⟩ (fun _ _ => Iff.rfl)⟩
  · exact ⟨⟨trivial, fun r h => h⟩, ⟨false, rfl⟩, fun ⟨_, _, _, h⟩ => h trivial,
      fun _ _ _ _ _ => trivial, fun h => h true rfl (fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)⟩
  · exact cf_no_terminal
  · exact fun _ _ _ A a t c hs hf hn hi ht hc hb => collapse_independent A a t c hs hf hn hi ht hc hb
  · intro _ _ _ A a r t hs hn hi hc he hct
    exact hi a r t he hct (fun v hv => ⟨hn a r t he v hv, hs r t v hc⟩)
  · exact cf_no_bccf
  · intro _ _ _ A w r f hw hr hf he
    exact hw f he (fun v hv => ⟨fun _ => hf v hv, fun _ => hr v hv⟩)
  · refine ⟨rfl, ⟨rfl, trivial⟩, fun v => Iff.rfl, Bool.noConfusion⟩
  · refine ⟨⟨rfl, ?_, ⟨fun _ => rs_terminal_nature, fun _ => rs_terminal_brute⟩⟩,
      ⟨rfl, ?_, fun h => ?_⟩⟩
    · exact RivalFact.noConfusion
    · exact RivalFact.noConfusion
    · obtain ⟨_, _, _, hn⟩ := h.1 ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩
      exact hn trivial

theorem foundationNormTest : FoundationNormTest := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ A a t hc hx hs hf hn hwf hnorm => norm_implication A a t hc hx hs hf hn hwf hnorm
  · exact ⟨ns_not_contingent, ⟨false, rfl, rfl⟩, ns_single, ns_factive, ns_nec, ns_wf, ns_nobrute⟩
  · refine ⟨is_cont, is_ne, ?_, is_factive, is_nec, is_wf, is_norm⟩
    intro x y _ _ _ _
    rfl
  · exact ⟨tw_cont _, ⟨.left, tw_left⟩, tw_not_single, tw_factive, tw_nec, tw_wf, tw_norm⟩
  · refine ⟨ft_cont, ft_explained, ?_, ft_notfactive, ft_nec, ft_wf, ?_⟩
    · intro x _ hx
      exact (ft_no_terminal x hx).elim
    · intro s _ h
      exact (ft_no_terminal s h.1).elim
  · exact ⟨g_choice false, ⟨.ground, rfl⟩, gf_single, g_factive false, gf_not_nec, gf_wf,
      fun s _ _ hb => g_nobrute false s hb⟩
  · intro a
    obtain ⟨c, hc⟩ := cf_some_contingent a
    refine ⟨c, hc, cf_factPSR a c hc.1, ?_, cf_factive, cf_nec, cf_not_wf a, ?_⟩
    · intro x _ hx
      exact (cf_no_terminal a x hx).elim
    · intro s _ h
      exact (cf_no_terminal a s h.1).elim
  · exact ⟨bt_contingent _, ⟨.terminus, rfl⟩, bt_single, bt_factive, bt_nec, bt_wf,
      fun h => h _ _ bt_foundation ⟨bt_contingent _, bt_not_explained⟩,
      bt_foundation, ⟨bt_contingent _, bt_not_explained⟩⟩
  · exact ⟨law_foundation, ⟨law_cont, law_ne⟩, fun h => h _ _ law_foundation ⟨law_cont, law_ne⟩⟩
  · exact ⟨tw_norm, ⟨tw_cont _, tw_ne_left⟩, ⟨tw_cont _, tw_ne_right⟩, tw_left, tw_right⟩
  · exact ⟨is_norm, is_cont, is_ne⟩
  · refine ⟨fun s _ _ hb => g_nobrute true s hb, ?_, fun s _ _ hb => g_nobrute false s hb,
      fun h => g_no_self (h _ _ gf_foundation), gf_foundation⟩
    intro s _ _
    cases s
    · exact ⟨.ground, rfl⟩
    · exact ⟨.ground, rfl⟩
  · intro _ _ _ A w s _ hF
    exact ⟨s, rfl, hF.1.1⟩
  · refine ⟨fun h => h _ _ scene_foundation scene_brute, ⟨.event, rfl, rfl⟩, scene_brute,
      scene_foundation, blank_unsupported, fun s _ _ hb => g_nobrute false s hb,
      ⟨.ground, rfl, rfl⟩, fun ⟨_, h⟩ => h⟩
  · intro _ _ _ A hf
    exact ⟨rfl, rfl, fun w f ⟨r, he⟩ => ⟨f, rfl, (hf w r f he).2⟩⟩
  · refine ⟨bt_not_explained, ⟨.terminus, rfl, rfl⟩, fun h => ?_⟩
    exact h false .terminus .terminus ⟨rfl, rfl⟩
      ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩ (fun _ _ => Iff.rfl)

end TruthCore.Results.Explanation.StoppingPoints
