import TruthCore.Explanation.BorrowedExercise
import TruthCore.Results.Causality.DerivativeJointPower.Solution
import TruthCore.Results.Explanation.CondensationSufficiency.Solution
namespace TruthCore.Results.Explanation.BorrowedExercise
open TruthCore.Causality TruthCore.Logic.Regress
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Explanation.JointCooperation (NecessaryIn)
open TruthCore.Explanation.BorrowedExercise
open TruthCore.Results.Causality.DerivativeJointPower (trap_obstruction source_free_control branch_trap)
variable {B E G S : Type}

theorem retained_iff (m : Exercise B E G S) (cap : S → E → Prop) (e : E) :
    Retained m cap e ↔ ¬ Borrowed m cap e := by
  simp only [Retained, Borrowed]; push Not; rfl

theorem supply_mono {h : Groups E G} {I J : E → Prop} (hij : ∀ x, I x → J x) {e : E}
    (hs : Supply h I e) : Supply h J e := by
  induction hs with
  | intrinsic e hi => exact .intrinsic e (hij e hi)
  | joint g hg _ ih => exact .joint g hg ih

/-- The occurring events without Supply form a trap, given that an occurring event
outside `I` has a lender and satisfies `P`. -/
theorem fork (m : Exercise B E G S) (I P : E → Prop) (e : E)
    (hp : ∀ x, m.occurs m.actual x → ¬ I x → P x ∧ Lent m m.actual x)
    (he : m.occurs m.actual e) :
    Supply (lentGroups m) I e ∨ ∃ D, Descent m I e D ∧ ∀ x ∈ D, P x := by
  by_cases hs : Supply (lentGroups m) I e
  · exact .inl hs
  · refine .inr ⟨{x | m.occurs m.actual x ∧ ¬ Supply (lentGroups m) I x}, ⟨⟨he, hs⟩, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      exact ⟨hx.1, (hp x hx.1 fun hi => hx.2 (.intrinsic x hi)).2⟩
    · intro x hx hi
      exact hx.2 (.intrinsic x hi)
    · intro g hg hx
      by_contra hno
      push Not at hno
      apply hx.2
      refine .joint g hg fun c hc => ?_
      by_contra hcs
      exact hno c hc ⟨hg.2.2.2 c hc, hcs⟩
    · intro x hx
      exact (hp x hx.1 fun hi => hx.2 (.intrinsic x hi)).1

theorem descent_step {m : Exercise B E G S} {I : E → Prop} {e : E} {D : Set E}
    (hd : Descent m I e D) {x : E} (hx : x ∈ D) :
    ∃ y ∈ D, ∃ g, Lender m m.actual g ∧ m.groups.effect g = x ∧ y ∈ m.groups.contributors g := by
  obtain ⟨g, hg, hgx⟩ := (hd.2.1 x hx).2
  obtain ⟨y, hy, hyD⟩ := hd.2.2.2 g hg (by simpa [lentGroups, hgx] using hx)
  exact ⟨y, hyD, g, hg, hgx, hy⟩

/-- Injective-or-repeat split of a chain, without a finiteness premise. -/
theorem chain_split {m : Exercise B E G S} {P : E → Prop} {e : E} {f : Nat → E}
    (hf : Chain m P e f) : Regress m P e ∨ Circle m P e := by
  by_cases hi : Function.Injective f
  · exact .inl ⟨f, hf, hi⟩
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨a, b, hab, hne⟩ := hi
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact .inr ⟨f, hf, a, b, h, hab⟩
    · exact .inr ⟨f, hf, b, a, h, hab.symm⟩

theorem descent_split (m : Exercise B E G S) (I P : E → Prop) (e : E) (D : Set E)
    (hd : Descent m I e D) (hP : ∀ x ∈ D, P x) : Regress m P e ∨ Circle m P e := by
  classical
  let next : D → D := fun x => ⟨(descent_step hd x.2).choose, (descent_step hd x.2).choose_spec.1⟩
  let f : Nat → D := fun n => Nat.rec ⟨e, hd.1⟩ (fun _ x => next x) n
  refine chain_split (f := fun n => (f n).val) ⟨rfl, fun n => ⟨hP _ (f n).2, ?_⟩⟩
  exact (descent_step hd (f n).2).choose_spec.2

theorem lent_exercised (m : Exercise B E G S) (I : E → Prop) (e : E)
    (hs : Supply (lentGroups m) I e) : Supply m.exercisedGroups I e := by
  induction hs with
  | intrinsic e hi => exact .intrinsic e hi
  | joint g hg _ ih => exact .joint g ⟨hg.1, hg.2.1 rfl⟩ ih

theorem supply_occurs (m : Exercise B E G S) (I : E → Prop) (e : E) (hc : m.coherent)
    (hI : ∀ x, I x → m.occurs m.actual x) (hs : Supply (lentGroups m) I e) :
    m.occurs m.actual e := by
  induction hs with
  | intrinsic e hi => exact hI e hi
  | joint g hg _ _ => exact (hc.2 g (hg.2.1 rfl)).2.2

theorem wf_supply (m : Exercise B E G S) (e : E) (hw : WellFounded (lentGroups m).graph.edge)
    (he : m.occurs m.actual e) : Supply (lentGroups m) (SelfExercising m) e := by
  induction e using hw.induction with
  | _ x ih =>
    by_cases hl : Lent m m.actual x
    · obtain ⟨g, hg, rfl⟩ := hl
      refine .joint g hg fun c hc => ih c ⟨g, hg, rfl, .inl hc⟩ (hg.2.2.2 c hc)
    · exact .intrinsic x ⟨he, hl⟩

theorem self_own (m : Exercise B E G S) (cap : S → E → Prop) (ha : m.allowed m.actual)
    (hp : PowerRequired m cap) (e : E) (h : SelfExercising m e) : OwnActive m cap e :=
  ⟨h.1, m.actual, ha, hp e h.1, h.2⟩

theorem forks : Forks := by
  refine ⟨fun _ _ _ _ m cap e => retained_iff m cap e, ?_, ?_, ?_, ?_,
    fun _ _ _ _ => descent_split, fun _ _ _ _ => lent_exercised,
    fun _ _ _ _ => supply_occurs, fun _ _ _ _ => wf_supply⟩
  · intro _ _ _ _ m cap e ha hp he
    have hb := retained_iff m cap e
    refine ⟨?_, fun h => hb.1 h.2.1 h.1.1, fun h => h.2.2 h.1.2.2, fun h => h.2.2 h.1.2.2⟩
    · by_cases hl : Lent m m.actual e
      · by_cases hr : Retained m cap e
        · exact .inr (.inl ⟨hr, he, hl⟩)
        · exact .inl ⟨by_contra fun hn => hr (hb.2 hn), he, hl⟩
      · exact .inr (.inr ⟨he, hl⟩)
  · intro _ _ _ _ m e he
    rcases fork m (SelfExercising m) (fun _ => True) e
      (fun x hx hi => ⟨trivial, by_contra fun hn => hi ⟨hx, hn⟩⟩) he with h | ⟨D, hD, _⟩
    · exact .inl h
    · exact .inr ⟨D, hD⟩
  · intro _ _ _ _ m cap e ha hp he
    refine fork m (OwnActive m cap) (Instrument m cap) e (fun x hx hi => ?_) he
    have hb : Borrowed m cap x := by
      by_contra hn
      exact hi ⟨hx, (retained_iff m cap x).2 hn⟩
    have hl := hb m.actual ha (hp x hx)
    exact ⟨⟨hb, hx, hl⟩, hl⟩
  · intro _ _ _ _ m I e D hd
    exact trap_obstruction _ I D hd.2.2 e hd.1

theorem collapse : Collapse := by
  refine ⟨fun _ _ _ _ m cap e ha hp hs => supply_mono (self_own m cap ha hp) hs, ?_, ?_⟩
  · intro _ _ _ _ m cap e ha hp hP
    have key : ∀ x, OwnActive m cap x → SelfExercising m x := fun x h =>
      ⟨h.1, fun hl => (retained_iff m cap x).1 h.2 (hP x h.1 hl)⟩
    exact ⟨⟨key e, self_own m cap ha hp e⟩, supply_mono key, supply_mono (self_own m cap ha hp)⟩
  · intro _ _ _ _ m cap e ha hp hP he
    refine fork m (SelfExercising m) (Instrument m cap) e (fun x hx hi => ?_) he
    have hl : Lent m m.actual x := by_contra fun hn => hi ⟨hx, hn⟩
    exact ⟨⟨hP x hx hl, hx, hl⟩, hl⟩

/-! ## Witnesses -/

theorem trap_univ (m : Exercise B E G S) (I : E → Prop) (hI : ∀ x, ¬ I x) :
    Trap (lentGroups m) I Set.univ :=
  ⟨fun x _ => hI x, fun _ hg _ => let ⟨c, hc⟩ := hg.2.2.1; ⟨c, hc, trivial⟩⟩

theorem not_supply_of_lent (m : Exercise B E G S) (I : E → Prop) (hI : ∀ x, ¬ I x) (e : E) :
    ¬ Supply (lentGroups m) I e :=
  trap_obstruction _ I _ (trap_univ m I hI) e trivial

theorem supply_cases {h : Groups E G} {I : E → Prop} {e : E} (hs : Supply h I e) :
    I e ∨ ∃ g, h.admitted g ∧ h.effect g = e := by
  cases hs with
  | intrinsic e hi => exact .inl hi
  | joint g hg _ => exact .inr ⟨g, hg, rfl⟩

/-! ### The source-free chain -/

theorem chain_lender (n : Nat) : Lender chain true n :=
  ⟨trivial, fun _ => trivial, ⟨n + 1, Or.inl rfl⟩, fun _ _ => rfl⟩

theorem chain_lent (n : Nat) : Lent chain true n := ⟨n, chain_lender n, rfl⟩

theorem chain_not_lent (n : Nat) : ¬ Lent chain false n := by
  rintro ⟨g, hg, _⟩
  obtain ⟨c, hc⟩ := hg.2.2.1
  exact Bool.false_ne_true (hg.2.2.2 c hc)

theorem chain_chain (P : Nat → Prop) (hP : ∀ n, P n) (n : Nat) :
    Chain chain P n (fun k => n + k) :=
  ⟨rfl, fun k => ⟨hP _, n + k, chain_lender (n + k), rfl, Or.inl rfl⟩⟩

theorem chain_regress (P : Nat → Prop) (hP : ∀ n, P n) (n : Nat) : Regress chain P n :=
  ⟨_, chain_chain P hP n, fun _ _ h => Nat.add_left_cancel h⟩

theorem chain_instrument (n : Nat) : Instrument chain (capOccurs chain) n := by
  refine ⟨fun s _ hc => ?_, rfl, chain_lent n⟩
  cases (hc : s = true)
  exact chain_lent n

theorem chain_self_false (n : Nat) : ¬ SelfExercising chain n := fun h => h.2 (chain_lent n)

theorem instrument_regress : InstrumentRegress := by
  have hs := (source_free_control)
  refine ⟨hs.1, hs.2.1, hs.2.2.1, fun _ h => h, fun _ _ _ => (chain_instrument _).1,
    chain_instrument, chain_regress _ chain_instrument, fun n => ?_, fun n => ?_⟩
  · exact not_supply_of_lent _ _ (fun x h => (retained_iff _ _ x).1 h.2 (chain_instrument x).1) n
  · exact not_supply_of_lent _ _ chain_self_false n

theorem chain_retained (n : Nat) : Retained chain capAll n :=
  ⟨false, trivial, trivial, chain_not_lent n⟩

theorem chain_secondary (n : Nat) : Secondary chain capAll n :=
  ⟨chain_retained n, rfl, chain_lent n⟩

theorem secondary_regress : SecondaryRegress := by
  refine ⟨fun _ _ => trivial, fun hP => ?_, chain_secondary, fun n => .intrinsic n ⟨rfl, chain_retained n⟩,
    fun n => not_supply_of_lent _ _ chain_self_false n, chain_regress _ chain_secondary⟩
  exact (retained_iff _ _ 0).1 (chain_retained 0) (hP 0 rfl (chain_lent 0))

theorem selected_lent (n : Nat) : Lent selectedChain true n :=
  ⟨n, ⟨trivial, fun _ => trivial, ⟨n + 1, Or.inl rfl⟩, fun _ _ => rfl⟩, rfl⟩

theorem selected_instrument (n : Nat) : Instrument selectedChain capAll n := by
  refine ⟨fun s hs _ => ?_, rfl, selected_lent n⟩
  cases (hs : s = true)
  exact selected_lent n

theorem selected_collapse : SelectedCollapse :=
  ⟨⟨rfl, fun _ _ => ⟨trivial, fun _ _ => rfl, rfl⟩⟩, selected_instrument, fun n =>
    not_supply_of_lent _ _ (fun x h => (retained_iff _ _ x).1 h.2 (selected_instrument x).1) n⟩

/-! ### The rooted #634 branch -/

theorem rooted_source_not_lent (s : Bool) : ¬ Lent rooted s (node none) := by
  rintro ⟨g, _, hg⟩
  obtain ⟨y, hy⟩ := g.property
  have hv : g.val.val = none := congrArg Subtype.val hg
  change TruthCore.Results.Causality.GroundingAllowsRegress.link y.val g.val.val at hy
  simp [hv, TruthCore.Results.Causality.GroundingAllowsRegress.link] at hy

theorem rooted_lent (n : Nat) : Lent rooted true (node (some n)) :=
  ⟨group n, ⟨trivial, fun _ => trivial, ⟨node none, trivial⟩, fun _ _ => Or.inr rfl⟩, rfl⟩

theorem rooted_instrument (n : Nat) : Instrument rooted (capOccurs rooted) (node (some n)) := by
  refine ⟨fun s _ hc => ?_, Or.inr rfl, rooted_lent n⟩
  rcases hc with hi | hs
  · simp [intrinsic, node] at hi
  · cases (hs : s = true)
    exact rooted_lent n

theorem rooted_branch : RootedBranch := by
  refine ⟨fun _ h => h, ⟨Or.inl rfl, rooted_source_not_lent true⟩, fun _ _ => Or.inl rfl,
    .intrinsic _ ⟨Or.inl rfl, true, trivial, Or.inl rfl, rooted_source_not_lent true⟩,
    rooted_instrument, fun n => ?_⟩
  refine trap_obstruction (lentGroups rooted) _ branch ⟨?_, fun g _ hd => branch_trap.2 g trivial hd⟩ (node (some n)) ⟨n, rfl⟩
  rintro e ⟨k, hk⟩ h
  have he : e = node (some k) := Subtype.ext hk
  subst he
  exact (retained_iff _ _ _).1 h.2 (rooted_instrument k).1

/-! ### The circle -/

theorem circle_mem (e : Bool) : (!e) ∈ circleExercise.groups.contributors e := by
  show (!e) ≠ e
  cases e <;> decide

theorem circle_lender (e : Bool) : Lender circleExercise true e :=
  ⟨trivial, fun _ => trivial, ⟨!e, circle_mem e⟩, fun _ _ => rfl⟩

theorem circle_lent (e : Bool) : Lent circleExercise true e := ⟨e, circle_lender e, rfl⟩

theorem circle_instrument (e : Bool) :
    Instrument circleExercise (capOccurs circleExercise) e := by
  refine ⟨fun s _ hc => ?_, rfl, circle_lent e⟩
  cases (hc : s = true)
  exact circle_lent e

theorem instrument_circle : InstrumentCircle := by
  refine ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => rfl, rfl⟩⟩, ?_, circle_instrument, ?_, ?_⟩
  · intro g s _ hm
    exact hm (!g) (Or.inl (circle_mem g))
  · intro e
    refine ⟨fun n => Nat.rec e (fun _ x => !x) n,
      ⟨rfl, fun n => ⟨circle_instrument _, _, circle_lender _, rfl, circle_mem _⟩⟩, 0, 2, by decide, ?_⟩
    show e = !!e
    simp
  · exact not_supply_of_lent _ _ fun x h =>
      (retained_iff _ _ x).1 h.2 (circle_instrument x).1

/-! ### Same graph, different records -/

section records
open TruthCore.Explanation.CondensationSufficiency
open TruthCore.Results.Explanation.CondensationSufficiency (conj_graph disj_graph onOff_coherent)

theorem onOff_not_lent {G : Type} (h : Groups Ev G) (hs : ∀ g, h.effect g ≠ .s) (b : Bool) :
    ¬ Lent (onOff h everyScenario) b .s := by
  rintro ⟨g, _, hg⟩
  exact hs g hg

theorem onOff_s_own {G : Type} (h : Groups Ev G) (hs : ∀ g, h.effect g ≠ .s) :
    OwnActive (onOff h everyScenario) (capOccurs (onOff h everyScenario)) .s :=
  ⟨Or.inl rfl, true, trivial, Or.inl rfl, onOff_not_lent h hs true⟩

theorem conj_effect (g : Bool) : conj.effect g ≠ .s := by cases g <;> decide
theorem disj_effect (g : DisjGroup) : disj.effect g ≠ .s := by cases g <;> decide

theorem conj_lent_t : Lent (onOff conj everyScenario) true .t :=
  ⟨true, ⟨trivial, fun _ => trivial, ⟨.s, Or.inl rfl⟩, fun _ _ => Or.inr rfl⟩, rfl⟩
theorem conj_lent_u : Lent (onOff conj everyScenario) true .u :=
  ⟨false, ⟨trivial, fun _ => trivial, ⟨.t, rfl⟩, fun _ _ => Or.inr rfl⟩, rfl⟩
theorem disj_lent_t : Lent (onOff disj everyScenario) true .t :=
  ⟨.fromS, ⟨trivial, fun _ => trivial, ⟨.s, rfl⟩, fun _ _ => Or.inr rfl⟩, rfl⟩

theorem onOff_true_of {G : Type} {h : Groups Ev G} {s : Bool} {e : Ev} (he : e ≠ .s)
    (hc : capOccurs (onOff h everyScenario) s e) : s = true := by
  rcases hc with h0 | h0
  · exact (he h0).elim
  · exact h0

theorem conj_borrowed_t : Borrowed (onOff conj everyScenario)
    (capOccurs (onOff conj everyScenario)) .t := fun s _ hc => by
  cases onOff_true_of (by decide) hc
  exact conj_lent_t

theorem conj_borrowed_u : Borrowed (onOff conj everyScenario)
    (capOccurs (onOff conj everyScenario)) .u := fun s _ hc => by
  cases onOff_true_of (by decide) hc
  exact conj_lent_u

theorem record_control : RecordControl := by
  refine ⟨conj_graph.trans disj_graph.symm, onOff_coherent _ _ trivial (fun _ => trivial),
    onOff_coherent _ _ trivial (fun _ => trivial), ⟨conj_borrowed_t, Or.inr rfl, conj_lent_t⟩,
    ⟨fun s _ hc => ?_, Or.inr rfl, disj_lent_t⟩, ?_, ?_⟩
  · cases onOff_true_of (by decide) hc
    exact disj_lent_t
  · refine trap_obstruction _ _ cycleEvents ⟨?_, fun g _ hd => ?_⟩ _ (Or.inl rfl)
    · rintro e (rfl | rfl) h
      · exact (retained_iff _ _ _).1 h.2 conj_borrowed_t
      · exact (retained_iff _ _ _).1 h.2 conj_borrowed_u
    · cases g
      · exact ⟨.t, rfl, Or.inl rfl⟩
      · exact ⟨.u, Or.inr rfl, Or.inr rfl⟩
  · refine .joint DisjGroup.fromS ⟨trivial, fun _ => trivial, ⟨.s, rfl⟩, fun _ _ => Or.inr rfl⟩ ?_
    intro e he
    have he' : e = Ev.s := he
    subst he'
    exact .intrinsic _ (onOff_s_own disj disj_effect)

end records

/-! ### Finite exercises -/

theorem finite_lender : Lender finiteExercise true () :=
  ⟨trivial, fun _ => trivial, ⟨false, rfl⟩, fun _ _ => rfl⟩

theorem finite_lent : Lent finiteExercise true true := ⟨(), finite_lender, rfl⟩

theorem finite_not_lent_false (s : Bool) : ¬ Lent finiteExercise s false := by
  rintro ⟨_, _, h⟩
  exact Bool.noConfusion h

theorem finite_not_lent_off : ¬ Lent finiteExercise false true := by
  rintro ⟨_, hg, _⟩
  exact Bool.false_ne_true (hg.2.2.2 false rfl)

theorem finite_supply_from (I : Bool → Prop) (hI : I false) :
    Supply (lentGroups finiteExercise) I true := by
  refine .joint () finite_lender fun e he => ?_
  have he' : e = false := he
  subst he'
  exact .intrinsic _ hI

theorem founded_controls : FoundedControls := by
  have hself : SelfExercising finiteExercise false := ⟨rfl, finite_not_lent_false true⟩
  refine ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => rfl, rfl⟩⟩, ⟨fun s _ hc => ?_, rfl, finite_lent⟩,
    hself, fun _ _ => Or.inl rfl,
    finite_supply_from _ ⟨rfl, true, trivial, Or.inl rfl, finite_not_lent_false true⟩,
    ⟨fun s _ hc => ?_, rfl, finite_lent⟩, fun h => Bool.false_ne_true (h false trivial),
    ⟨rfl, true, trivial, rfl, finite_not_lent_false true⟩,
    finite_supply_from _ ⟨rfl, true, trivial, rfl, finite_not_lent_false true⟩,
    fun h => Bool.false_ne_true (h false trivial),
    ⟨⟨false, trivial, trivial, finite_not_lent_off⟩, rfl, finite_lent⟩,
    finite_supply_from _ ⟨rfl, true, trivial, trivial, finite_not_lent_false true⟩,
    finite_supply_from _ hself⟩
  · rcases hc with h | h
    · exact Bool.noConfusion h
    · cases (h : s = true); exact finite_lent
  · cases (hc : s = true); exact finite_lent

theorem power_omission : PowerOmission := by
  refine ⟨fun h => h false rfl, fun _ _ h => h.elim, fun hs => ?_, ?_⟩
  · rcases supply_cases hs with ⟨_, _, _, h, _⟩ | ⟨_, _, h⟩
    · exact h
    · exact Bool.noConfusion h
  · rintro ⟨D, h, hD, _⟩
    exact finite_not_lent_false true (hD false h).2

theorem lender_omissions : LenderOmissions := by
  refine ⟨.joint () trivial fun _ h => h.elim, fun m hm hl => ?_, fun s _ hm => hm false (Or.inl rfl), ⟨rfl, ?_⟩⟩
  · obtain ⟨g, hg, _⟩ := hl
    obtain ⟨c, hc⟩ := hg.2.2.1
    rw [hm] at hc
    exact hc
  · rintro ⟨_, hg, _⟩
    exact hg.2.1 rfl

theorem certificate : TruthCore.Explanation.BorrowedExercise.Certificate :=
  ⟨forks, collapse, instrument_regress, secondary_regress, selected_collapse, rooted_branch,
    instrument_circle, record_control, founded_controls, power_omission, lender_omissions⟩

end TruthCore.Results.Explanation.BorrowedExercise
