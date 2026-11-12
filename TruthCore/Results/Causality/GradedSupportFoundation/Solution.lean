module

public import TruthCore.Causality.GradedSupportFoundation
public import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution
public import TruthCore.Results.Causality.SpineRivalsRootEsse.Solution

@[expose] public section

namespace TruthCore.Results.Causality.GradedSupportFoundation

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.GradedSupportFoundation
open TruthCore.Causality.GradedSupportFoundation.Control
open TruthCore.Causality.Round2Grounding (ActualGroundIsMoreInEsse)
open TruthCore.Causality.Round3FourthWay (NoInfiniteAscentInBeing)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)

/-- Well-foundedness of a relation on a subtype lifts to a relation on the whole
carrier that relates only members of the subtype, along the subtype relation. -/
theorem wf_of_subtype {B : Type} {P : B → Prop} {r : {b // P b} → {b // P b} → Prop}
    (hr : WellFounded r) {s : B → B → Prop}
    (hs : ∀ y x, s y x → ∃ hy : P y, ∃ hx : P x, r ⟨y, hy⟩ ⟨x, hx⟩) :
    WellFounded s := by
  have key : ∀ a : {b // P b}, Acc s a.1 := by
    intro a
    induction a using hr.induction with
    | _ a ih =>
      exact Acc.intro _ fun y hyx => by
        obtain ⟨hy, _, h⟩ := hs y a.1 hyx
        exact ih ⟨y, hy⟩ h
  exact ⟨fun x => Acc.intro x fun y hyx => by
    obtain ⟨hy, _, _⟩ := hs y x hyx
    exact key ⟨y, hy⟩⟩

/-- The global no-infinite-ascent premise implies its restriction to actual
concreta at `w`. -/
theorem actualAscentWFOfGlobal {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hNIA : NoInfiniteAscentInBeing MoreIn esse) :
    NoInfiniteAscentAmongActualConcreta m w MoreIn esse :=
  Subrelation.wf (fun {_ _} h => h.2.2) hNIA

/-- The global no-infinite-ascent premise implies its restriction to concreta
necessary from `w`. -/
theorem necessaryAscentWFOfGlobal {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hNIA : NoInfiniteAscentInBeing MoreIn esse) :
    NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse :=
  Subrelation.wf (fun {_ _} h => h.2.2.2.2) hNIA

/-- Well-founded actual grounding, without a numeric rank: actual concrete
grounding at `w` ascends the rigid comparison `MoreIn esse`, which has no
infinite ascent among actual concreta at `w`. A descending grounding chain among
actual concreta would be an infinite ascent in esse among them. -/
theorem actualGroundingWFOfAscent {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : ActualGroundIsMoreInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongActualConcreta m w MoreIn esse) :
    ActualGroundingWF m w :=
  Subrelation.wf
    (r := InvImage (fun y x => ActualConcrete m w y ∧ ActualConcrete m w x ∧ MoreIn esse y x)
      Subtype.val)
    (fun {a b} h => ⟨a.2, b.2, hUp a.1 b.1 a.2 b.2 h⟩) (InvImage.wf _ hNIA)

/-- J2 without the no-novel-edge condition: support between concreta necessary
from `w`, at every admitted world, ascends the same rigid comparison, which has no
infinite ascent among concreta necessary from `w`. Every edge of the cross-world
union is one ascent step. -/
theorem unionWFOfAscent {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    ConcreteNecessaryUnionWF m w :=
  Subrelation.wf
    (r := InvImage (fun y x => m.concrete y ∧ m.concrete x ∧ NecessaryAt m.ontic w y ∧
      NecessaryAt m.ontic w x ∧ MoreIn esse y x) Subtype.val)
    (fun {a b} h => by
      obtain ⟨ha, hb, v, hv, hg⟩ := h
      exact ⟨a.2, b.2, ha, hb, hUp v a.1 b.1 a.2 b.2 ha hb hv hg⟩)
    (InvImage.wf _ hNIA)

/-- The mutual-support rival of J2 is excluded by a rigid well-founded grade
that support between necessary concreta ascends, with no reflexivity, actual
well-foundedness or no-novel-edge premise: two necessary concreta supporting
each other at two worlds would each be more in esse than the other. -/
theorem mutualSupportExcludedByGrade {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hUp : NecessarySupportAscendsInEsse m w MoreIn esse)
    (hNIA : NoInfiniteAscentAmongNecessaryConcreta m w MoreIn esse) :
    NoNecessaryConcretaMutualSupport m w := fun h =>
  TruthCore.Results.Causality.SpineRivalsRootEsse.mutualSupport_excludes m w h
    (unionWFOfAscent m w MoreIn esse hUp hNIA)

/-- The ascent premise from the Aristotelian cause principle: a distinct cause
of a quality in another is more such than it; an actual concrete ground of an
actual concretum is a distinct cause of its being. -/
theorem groundMoreInEsseOfCause {W B R : Type} (m : Profile W B) (w : W)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hBridge : ActualGroundIsDistinctEsseCause m w CausesIn esse) :
    ActualGroundIsMoreInEsse m w MoreIn esse := by
  intro a b ha hb hg
  obtain ⟨hne, hc⟩ := hBridge a b ha hb hg
  exact hCause a b esse hne hc

/-- Ascent of support at every world from the Aristotelian cause principle and
the every-world ground-cause bridge. -/
theorem everywhereAscentOfCause {W B R : Type} (m : Profile W B)
    (CausesIn : B → B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (hCause : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hBridge : SupportIsDistinctEsseCauseEverywhere m CausesIn esse) :
    SupportAscendsInEsseEverywhere m MoreIn esse := by
  intro v a b ha hb hv hg
  obtain ⟨hne, hc⟩ := hBridge v a b ha hb hv hg
  exact hCause a b esse hne hc

/-- Ascent of support at every world implies ascent of support between
necessary concreta. -/
theorem necessaryAscentOfEverywhere {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hU : SupportAscendsInEsseEverywhere m MoreIn esse) :
    NecessarySupportAscendsInEsse m w MoreIn esse :=
  fun v a b ha hb _ _ hv hg => hU v a b ha hb hv hg

/-- Ascent of support at every world implies ascent of actual grounding at `w`. -/
theorem actualAscentOfEverywhere {W B R : Type} (m : Profile W B) (w : W)
    (MoreIn : R → B → B → Prop) (esse : R)
    (hU : SupportAscendsInEsseEverywhere m MoreIn esse) :
    ActualGroundIsMoreInEsse m w MoreIn esse :=
  fun a b ha hb hg => hU w a b ha.1 hb.1 ha.2 hg

/-- Converse characterization: well-founded actual grounding yields a rigid
grade with no infinite ascent that actual grounding ascends (actual grounding
itself, extended by nothing). -/
theorem gradedOfActualGroundingWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : GradedActualGrounding m w :=
  ⟨fun _ a b => ∃ _ : ActualConcrete m w a, ∃ _ : ActualConcrete m w b, m.grounds w a b,
    fun _ _ ha hb hg => ⟨ha, hb, hg⟩,
    wf_of_subtype hWF fun _ _ h => h⟩

/-- Some well-founded rigid grade ascended by actual grounding gives well-founded
actual grounding. -/
theorem actualGroundingWFOfGraded {W B : Type} (m : Profile W B) (w : W)
    (h : GradedActualGrounding m w) : ActualGroundingWF m w := by
  obtain ⟨MoreIn, hUp, hNIA⟩ := h
  exact actualGroundingWFOfAscent m w MoreIn () hUp (actualAscentWFOfGlobal m w MoreIn () hNIA)

/-- Converse characterization: J2 yields a rigid grade with no infinite ascent
that support between necessary concreta ascends (the union itself). -/
theorem gradedOfUnionWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ConcreteNecessaryUnionWF m w) : GradedNecessarySupport m w :=
  ⟨fun _ a b => ∃ ha : m.concrete a, ∃ hb : m.concrete b,
      UnionNecessarySupport (concreteOntic m) (concreteSupport m) w ⟨a, ha⟩ ⟨b, hb⟩,
    fun v _ _ ha hb na nb hv hg => ⟨ha, hb, na, nb, v, hv, hg⟩,
    wf_of_subtype hWF fun _ _ h => h⟩

/-- Some well-founded rigid grade ascended by necessary support gives J2. -/
theorem unionWFOfGraded {W B : Type} (m : Profile W B) (w : W)
    (h : GradedNecessarySupport m w) : ConcreteNecessaryUnionWF m w := by
  obtain ⟨MoreIn, hUp, hNIA⟩ := h
  exact unionWFOfAscent m w MoreIn () hUp (necessaryAscentWFOfGlobal m w MoreIn () hNIA)

/-! ## Controls -/

/-- `boolGrade` has no infinite ascent: only `false` is above anything, and
nothing is above `false`. -/
theorem boolGrade_wf : NoInfiniteAscentInBeing boolGrade () := by
  constructor
  intro b
  apply Acc.intro
  intro a ha
  have ha0 : a = false := ha.1
  apply Acc.intro
  intro c hc
  exact Bool.noConfusion (ha0.symm.trans hc.2)

theorem reversedGrade_wf : NoInfiniteAscentInBeing reversedGrade () := by
  constructor
  intro b
  apply Acc.intro
  intro a ha
  have ha1 : a = true := ha.1
  apply Acc.intro
  intro c hc
  exact Bool.noConfusion (ha1.symm.trans hc.2)

theorem jointWitness : GradedJointWitness := by
  have hU : SupportAscendsInEsseEverywhere witnessProfile boolGrade () := by
    intro v a b _ _ _ hg
    exact ⟨hg.1, hg.2.1⟩
  refine ⟨TruthCore.Results.Causality.NecessaryConcreteUnderived.jointWitness, hU, ?_,
    necessaryAscentOfEverywhere _ _ _ _ hU, actualAscentOfEverywhere _ _ _ _ hU,
    boolGrade_wf, ?_, ?_, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · intro v a b _ _ _ hg
    refine ⟨?_, hg.1, hg.2.1⟩
    intro hab
    exact Bool.noConfusion ((hab.symm.trans hg.1).symm.trans hg.2.1)
  · intro a b _ _ hg
    refine ⟨?_, hg.1, hg.2.1⟩
    intro hab
    exact Bool.noConfusion ((hab.symm.trans hg.1).symm.trans hg.2.1)
  · intro y x _ _ hc
    exact hc

theorem descendingGrade : DescendingGrade := by
  refine ⟨TruthCore.Results.Causality.NecessaryConcreteUnderived.jointWitness.2.1,
    reversedGrade_wf, ?_⟩
  intro h
  have := h false true ⟨trivial, Or.inl rfl⟩ ⟨trivial, Or.inr rfl⟩ ⟨rfl, rfl, rfl⟩
  exact Bool.noConfusion this.1

theorem offWorldAscent : OffWorldAscent := by
  have hU : SupportAscendsInEsseEverywhere Control.uncoveredEdge boolGrade () := by
    intro v a b _ _ _ hg
    exact ⟨hg.2.1, hg.2.2⟩
  refine ⟨hU, necessaryAscentOfEverywhere _ _ _ _ hU, boolGrade_wf,
    unionWFOfAscent _ _ _ _ (necessaryAscentOfEverywhere _ _ _ _ hU)
      (necessaryAscentWFOfGlobal _ _ _ _ boolGrade_wf), ?_, ?_⟩
  · intro hCov
    obtain ⟨c, -, -, h1, -⟩ := hCov true false true trivial trivial (fun _ _ => trivial) trivial
      ⟨rfl, rfl, rfl⟩
    nomatch h1
  · intro h
    obtain ⟨h1, -⟩ := h true ⟨false, trivial⟩ ⟨true, trivial⟩ (fun _ _ => trivial)
      (fun _ _ => trivial) trivial ⟨rfl, rfl, rfl⟩
    nomatch h1

/-- The rotating triangle's union is not well-founded. -/
theorem triangle_not_unionWF : ¬ ConcreteNecessaryUnionWF Control.rotatingTriangle .t0 := by
  intro hWF
  have hEdge : ∀ x : {b // Control.rotatingTriangle.concrete b}, ∃ y,
      UnionNecessarySupport (concreteOntic Control.rotatingTriangle)
        (concreteSupport Control.rotatingTriangle) .t0 y x := by
    intro x
    obtain ⟨x, hx⟩ := x
    cases x with
    | t0 => exact ⟨⟨.t2, trivial⟩, fun _ _ => trivial, fun _ _ => trivial, .t2, trivial,
        Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
    | t1 => exact ⟨⟨.t0, trivial⟩, fun _ _ => trivial, fun _ _ => trivial, .t0, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩⟩
    | t2 => exact ⟨⟨.t1, trivial⟩, fun _ _ => trivial, fun _ _ => trivial, .t1, trivial,
        Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  have key : ∀ x : {b // Control.rotatingTriangle.concrete b}, False := by
    intro x
    induction x using hWF.induction with
    | _ x ih =>
      obtain ⟨y, hy⟩ := hEdge x
      exact ih y hy
  exact key ⟨.t0, trivial⟩

/-- The rooted pair's union is not well-founded: `t1` and `t2` support each other
at different worlds. -/
theorem pair_not_unionWF : ¬ ConcreteNecessaryUnionWF Control.rootedPair false := by
  intro hWF
  let P : {b // Control.rootedPair.concrete b} → Prop := fun x => x.1 = .t1 ∨ x.1 = .t2
  have hEdge : ∀ x, P x → ∃ y, P y ∧
      UnionNecessarySupport (concreteOntic Control.rootedPair)
        (concreteSupport Control.rootedPair) false y x := by
    intro x hx
    obtain ⟨x, hc⟩ := x
    rcases hx with h | h
    · subst h
      exact ⟨⟨.t2, trivial⟩, Or.inr rfl, fun _ _ => trivial, fun _ _ => trivial, true,
        trivial, Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · subst h
      exact ⟨⟨.t1, trivial⟩, Or.inl rfl, fun _ _ => trivial, fun _ _ => trivial, false,
        trivial, Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  have key : ∀ x, P x → False := by
    intro x
    induction x using hWF.induction with
    | _ x ih =>
      intro hx
      obtain ⟨y, hy, hyx⟩ := hEdge x hx
      exact ih y hyx hy
  exact key ⟨.t1, trivial⟩ (Or.inl rfl)

theorem pair_underived : NecessaryConcreteUnderivedAt Control.rootedPair false := by
  refine ⟨.t0, trivial, trivial, fun _ _ => trivial, ?_⟩
  intro v a _ _ hg
  rcases hg with ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ <;> nomatch h

theorem noGradeForRivals : NoGradeForRivals :=
  ⟨fun _ MoreIn esse h => triangle_not_unionWF (unionWFOfAscent _ _ MoreIn esse h.1 h.2),
    fun _ MoreIn esse h => pair_not_unionWF (unionWFOfAscent _ _ MoreIn esse h.1 h.2),
    pair_underived⟩

/-- All graded-foundation controls hold. -/
theorem controls : Controls :=
  ⟨jointWitness, descendingGrade, offWorldAscent, noGradeForRivals⟩

end TruthCore.Results.Causality.GradedSupportFoundation
