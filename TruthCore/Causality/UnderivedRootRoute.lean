import TruthCore.Causality.NecessaryRootFork
import TruthCore.Causality.NecessarilyUnderived

/-!
# From actual existence to a necessarily underived ground (#487)

Source-free and stipulative: nothing here is attributed to any author, and nothing
shows that any premise is true or that any model is metaphysically possible. Rival
names below are labels for models, not reports of anyone's view.

The route has three steps, each with its own premises:

1. *Actual existence to an actual root*: inhabitedness and `ActualGroundingWF`.
2. *Actual root to a necessary root*: `EveryContingentGroundedAt`.
3. *Necessary root to a necessarily underived ground*: `NecessarySupportIsPresent`
   and `ActualSupportersConcrete`. Rootness is world-relative and concrete-relative,
   so steps 1 and 2 do not give this step.

Each premise excludes one rival, and `UnderivedRouteExit` says that these are the
only exits. Coverage only: the exits overlap and no exit is refuted.

| Premise omitted | Rival surviving |
|---|---|
| inhabitedness | no actual concretum at all |
| well-foundedness | circular support, or endless descent |
| closing premise | a brute contingent root |
| support is present | support of a necessary being that varies with the world |
| supporters concrete | abstract support of concreta, whether founded or not |

`supportsEsse` of `NECESSARILY-UNDERIVED` is instantiated at the profile's selected
relation `m.grounds`. It is a parameter there, so this is a choice of relation and not
an identification of `grounds` with efficient causation.

What the conclusion supplies is limited. Every actual concretum descends from such a
ground, under step 2's and step 3's premises. But in `GroundLimits` all five
clauses hold while there are two such grounds with no ancestry between them, one grounding a
contingent concretum that is absent at a world where its ground exists. So the
premises give neither unity nor a ground that entails its effect.
-/
namespace TruthCore.Causality.UnderivedRootRoute

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround GroundAncestor)
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryRootFork
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- Open premise: whatever supports a being necessary from `w`, at any world where
that supporter exists, also exists at `w` and supports it at `w`. Weaker than
`NecessaryPredecessorLifting`, which also makes the supporter necessary. -/
def NecessarySupportIsPresent (m : Profile W B) (w : W) : Prop :=
  ∀ v y x, NecessaryAt m.ontic w x → m.ontic.ExistsAt v y → m.grounds v y x →
    PresentEsseSupport m.ontic m.grounds w y x

/-- Open premise: an existing supporter of an actual concretum at `w` is concrete.
An existing abstract ground of a concretum would falsify it. -/
def ActualSupportersConcrete (m : Profile W B) (w : W) : Prop :=
  ∀ y x, ActualConcrete m w x → m.ontic.ExistsAt w y → m.grounds w y x → m.concrete y

/-- `x` is an actual root at `w`, necessary from `w`, and has no existing supporter
at any world. Uniqueness, simplicity and intellect are not included. -/
def UnderivedRootAt (m : Profile W B) (w : W) (x : B) : Prop :=
  ActualRoot m w x ∧ NecessaryAt m.ontic w x ∧
    ∀ v, NoExistingSupportAt m.ontic m.grounds v x

/-- Every actual concretum at `w` has an actual concrete ground-ancestor, possibly
itself, that is an `UnderivedRootAt`. Different concreta may have different ones. -/
def EveryConcretumDescendsFromUnderivedRoot (m : Profile W B) (w : W) : Prop :=
  ∀ x, ActualConcrete m w x → ∃ r, UnderivedRootAt m w r ∧ GroundAncestor m w r x

/-- The four exits from the route, alongside its conclusion. Not exclusive. -/
def UnderivedRouteExit (m : Profile W B) (w : W) : Prop :=
  NecessarilyUnderived m.ontic m.grounds w ∨ ¬ ActualGroundingWF m w ∨
    ContingentRootAt m w ∨ ¬ NecessarySupportIsPresent m w ∨ ¬ ActualSupportersConcrete m w

/-! ## The route -/

/-- Steps 1 and 2, for every actual concretum: its ancestry reaches a necessary root. -/
theorem descendsFromNecessaryRoot (m : Profile W B) (w : W) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) (x : B)
    (hx : ActualConcrete m w x) :
    ∃ r, ActualRoot m w r ∧ NecessaryAt m.ontic w r ∧ GroundAncestor m w r x := by
  have walk : ∀ a : {x // ActualConcrete m w x},
      ∃ r, ActualRoot m w r ∧ NecessaryAt m.ontic w r ∧ GroundAncestor m w r a.1 := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      rcases hEM (∃ y, ActualConcreteGround m w y a.1) with ⟨y, hy⟩ | hnone
      · obtain ⟨r, hr, hn, hanc⟩ := ih ⟨y, hy.1, hy.2.1⟩ hy.2.2
        exact ⟨r, hr, hn, Relation.ReflTransGen.tail hanc hy⟩
      · have hr : ActualRoot m w a.1 := ⟨a.2, fun y hy => hnone ⟨y, hy⟩⟩
        rcases hEM (NecessaryAt m.ontic w a.1) with hn | hn
        · exact ⟨a.1, hr, hn, Relation.ReflTransGen.refl⟩
        · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
            (contingentRootOfNonnecessary m w hEM ⟨a.1, hr, hn⟩)).elim
  exact walk ⟨x, hx⟩

/-- Step 3, with no excluded middle. -/
theorem underivedOfNecessaryRoot (m : Profile W B) (w : W)
    (hPresent : NecessarySupportIsPresent m w) (hConcrete : ActualSupportersConcrete m w)
    (x : B) (hr : ActualRoot m w x) (hn : NecessaryAt m.ontic w x) :
    UnderivedRootAt m w x := by
  refine ⟨hr, hn, fun v y hy he => ?_⟩
  obtain ⟨hyw, hew⟩ := hPresent v y x hn hy he
  exact hr.2 y ⟨hConcrete y x hr.1 hyw hew, hyw, hew⟩

/-- Every actual concretum descends from a necessarily underived root. -/
theorem everyConcretumDescends (m : Profile W B) (w : W) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPresent : NecessarySupportIsPresent m w) (hConcrete : ActualSupportersConcrete m w) :
    EveryConcretumDescendsFromUnderivedRoot m w := by
  intro x hx
  obtain ⟨r, hr, hn, hanc⟩ := descendsFromNecessaryRoot m w hWF hDep hEM x hx
  exact ⟨r, underivedOfNecessaryRoot m w hPresent hConcrete r hr hn, hanc⟩

/-- The whole route: actual existence to a necessarily underived ground. -/
theorem necessarilyUnderivedOfGrounded (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hPresent : NecessarySupportIsPresent m w) (hConcrete : ActualSupportersConcrete m w) :
    NecessarilyUnderived m.ontic m.grounds w := by
  obtain ⟨x, hc, he⟩ := hPop
  obtain ⟨r, hu, _⟩ := everyConcretumDescends m w hWF hDep hEM hPresent hConcrete x ⟨hc, he⟩
  exact ⟨r, hu.1.1.2, hu.2.1, hu.2.2⟩

/-- Coverage: in an inhabited world, the conclusion holds or the rival takes an exit. -/
theorem underivedRouteExit (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hEM : ExcludedMiddle) :
    UnderivedRouteExit m w := by
  rcases hEM (ActualGroundingWF m w) with hWF | hWF
  · rcases hEM (ContingentRootAt m w) with hRoot | hRoot
    · exact Or.inr (Or.inr (Or.inl hRoot))
    · rcases hEM (NecessarySupportIsPresent m w) with hP | hP
      · rcases hEM (ActualSupportersConcrete m w) with hC | hC
        · exact Or.inl (necessarilyUnderivedOfGrounded m w hPop hWF
            ((everyContingentGrounded_iff_noContingentRoot m w hEM).mpr hRoot) hEM hP hC)
        · exact Or.inr (Or.inr (Or.inr (Or.inr hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
  · exact Or.inr (Or.inl hWF)

/-- `NecessaryPredecessorLifting` at the selected relation gives the weaker premise. -/
theorem presentOfLifting (m : Profile W B) (w : W)
    (h : NecessaryPredecessorLifting m.ontic m.grounds w) : NecessarySupportIsPresent m w :=
  fun v y x hn hy he => (h v y x hn hy he).2

/-! ## Controls -/

/-- A profile with universal accessibility. -/
def prof (E : W → B → Prop) (c : B → Prop) (g : W → B → B → Prop) : Profile W B :=
  { ontic := { frame := { access := fun _ _ => True }, ExistsAt := E, Causes := fun _ _ _ => False }
    concrete := c
    grounds := g }

/-- The rotating profile: at world `v`, `v` supports `!v`. -/
def rotating : Profile Bool Bool :=
  prof (fun _ _ => True) (fun _ => True) (fun v y x => y = v ∧ x = !v)

/-- The possible-contingent profile: `false` exists everywhere, `true` only at world
`true`, where it supports `false`. -/
def possibleContingent : Profile Bool Bool :=
  prof (fun v x => x = false ∨ v = true) (fun _ => True)
    (fun v y x => v = true ∧ y = true ∧ x = false)

/-- Three individuals. In `abstractSupport` only `d` is concrete; in `limitsProfile`
all are. -/
inductive Cell
  | d | a | b

/-- Support in the abstract model: `a` and `b` support each other, and `a` supports `d`. -/
def abstractGrounds : Cell → Cell → Prop
  | .d, .d => False
  | .d, .a => False
  | .d, .b => False
  | .a, .d => True
  | .a, .a => False
  | .a, .b => True
  | .b, .d => False
  | .b, .a => True
  | .b, .b => False

/-- The abstract-support profile. -/
def abstractSupport : Profile Unit Cell :=
  prof (fun _ _ => True) (fun y => y = .d) (fun _ => abstractGrounds)


/-- The five non-logical hypotheses of `necessarilyUnderivedOfGrounded`. -/
inductive Clause
  | inhabited | wellFounded | closing | present | concrete

/-- What each clause says of a profile. -/
def Clause.holds (m : Profile W B) (w : W) : Clause → Prop
  | .inhabited => InhabitedConcreteAt m.ontic m.concrete w
  | .wellFounded => ActualGroundingWF m w
  | .closing => EveryContingentGroundedAt m w
  | .present => NecessarySupportIsPresent m w
  | .concrete => ActualSupportersConcrete m w

/-- Each clause is omitted in a model in which the other four hold and no necessarily
underived individual exists. Excluded middle is not one of the clauses. -/
def EveryClauseOmitted : Prop :=
  ∀ c : Clause, ∃ (W B : Type) (m : Profile W B) (w : W),
    (∀ d : Clause, d ≠ c → d.holds m w) ∧ ¬ NecessarilyUnderived m.ontic m.grounds w

/-- Well-foundedness omitted by endless descent, with no cycle: every edge runs from a
larger number to a smaller one. -/
def EndlessDescentOmission : Prop :=
  ∃ (m : Profile Unit Nat),
    (∀ d : Clause, d ≠ .wellFounded → d.holds m ()) ∧
    ¬ NecessarilyUnderived m.ontic m.grounds () ∧ (∀ y x, m.grounds () y x → x < y)

/-- Steps 1 and 2 go through, a necessary actual root exists, and step 3's conclusion
fails. The remaining two clauses are stated by each use. -/
def RootWithoutUnderived (m : Profile W B) (w : W) : Prop :=
  InhabitedConcreteAt m.ontic m.concrete w ∧ ActualGroundingWF m w ∧
    EveryContingentGroundedAt m w ∧ (∃ x, ActualRoot m w x ∧ NecessaryAt m.ontic w x) ∧
    ¬ NecessarilyUnderived m.ontic m.grounds w

/-- Rotating support, in `rotating`: two necessary concreta support each other at
different worlds and never at one. A necessary actual root exists. Supporters of
necessary beings are all necessary, so only the transport of edges fails. -/
def RotatingSupport : Prop :=
  RootWithoutUnderived rotating false ∧ ActualSupportersConcrete rotating false ∧
    NoContingentGroundOfNecessary rotating.ontic rotating.grounds false ∧
    ¬ NoNovelNecessarySupport rotating.ontic rotating.grounds false

/-- Possible contingent support, in `possibleContingent`: a necessary concretum is
supported, at another world, by a contingent concretum absent from the selected world.
A necessary actual root exists. No support between necessary beings is novel. -/
def PossibleContingentSupport : Prop :=
  RootWithoutUnderived possibleContingent false ∧
    ActualSupportersConcrete possibleContingent false ∧
    NoNovelNecessarySupport possibleContingent.ontic possibleContingent.grounds false ∧
    ¬ NoContingentGroundOfNecessary possibleContingent.ontic possibleContingent.grounds false

/-- Abstract support, in `abstractSupport`: the only concretum is a necessary actual root
of the restricted relation, and it is supported by an abstract individual in an abstract
support cycle. `ActualGroundingWF` holds, since it does not reach abstract individuals.
All edges are transported, and `NecessaryPredecessorLifting` holds. -/
def AbstractSupport : Prop :=
  RootWithoutUnderived abstractSupport () ∧ NecessarySupportIsPresent abstractSupport () ∧
    NecessaryPredecessorLifting abstractSupport.ontic abstractSupport.grounds () ∧
    ¬ ActualSupportersConcrete abstractSupport ()

/-- The present-support premise is strictly weaker than lifting, and the route does not
need lifting: a contingent actual concretum supports a necessary one, so lifting fails,
all five clauses hold, and a necessarily underived individual exists. -/
def WeakerThanLifting : Prop :=
  ∃ (W B : Type) (m : Profile W B) (w : W),
    (∀ c : Clause, c.holds m w) ∧ ¬ NecessaryPredecessorLifting m.ontic m.grounds w ∧
    NecessarilyUnderived m.ontic m.grounds w

/-- All five clauses hold, and the conclusion supplies neither unity nor entailment of
effects. Two distinct underived roots have no ancestry between them. One grounds a
contingent concretum of which the other is no ancestor, and that concretum is absent at
an accessible world, where its ground exists. -/
def GroundLimits : Prop :=
  ∃ (W B : Type) (m : Profile W B) (w : W),
    (∀ c : Clause, c.holds m w) ∧
    ∃ r s c v, r ≠ s ∧ UnderivedRootAt m w r ∧ UnderivedRootAt m w s ∧
      ¬ GroundAncestor m w r s ∧ ¬ GroundAncestor m w s r ∧
      ActualConcreteGround m w r c ∧ ¬ GroundAncestor m w s c ∧
      m.ontic.frame.access w v ∧ m.ontic.ExistsAt v r ∧ ¬ m.ontic.ExistsAt v c ∧
      m.ontic.ExistsAt w c

/-- Coverage of every actual concretum, quantified over profiles. No inhabitedness. -/
def EveryConcretumDescendsPrinciple : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W), ActualGroundingWF m w →
    EveryContingentGroundedAt m w → ExcludedMiddle → NecessarySupportIsPresent m w →
    ActualSupportersConcrete m w → EveryConcretumDescendsFromUnderivedRoot m w

/-- Lifting at the selected relation gives the present-support premise. -/
def LiftingGivesPresent : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    NecessaryPredecessorLifting m.ontic m.grounds w → NecessarySupportIsPresent m w

/-- The control bundle. -/
def UnderivedRouteControls : Prop :=
  EveryConcretumDescendsPrinciple ∧ LiftingGivesPresent ∧ EveryClauseOmitted ∧
    EndlessDescentOmission ∧ RotatingSupport ∧ PossibleContingentSupport ∧ AbstractSupport ∧
    WeakerThanLifting ∧ GroundLimits

/-! ## Proofs of the controls -/

/-- Edges whose sources have no predecessors are well-founded. -/
theorem wf_of_heightOne (m : Profile W B) (w : W)
    (h : ∀ y x, m.grounds w y x → ∀ z, ¬ m.grounds w z y) : ActualGroundingWF m w :=
  ⟨fun a => ⟨a, fun b hb => ⟨b, fun _ hc => (h _ _ hb _ hc).elim⟩⟩⟩

/-- A single-world profile whose individuals all exist and are concrete. -/
def oneWorld (g : B → B → Prop) : Profile Unit B :=
  prof (fun _ _ => True) (fun _ => True) (fun _ => g)

theorem oneWorld_closing (g : B → B → Prop) : EveryContingentGroundedAt (oneWorld g) () :=
  fun _ _ _ hc => match hc with
    | ⟨_, _, _, habs⟩ => (habs True.intro).elim

theorem oneWorld_present (g : B → B → Prop) : NecessarySupportIsPresent (oneWorld g) () :=
  fun _ _ _ _ _ he => ⟨True.intro, he⟩

theorem oneWorld_concrete (g : B → B → Prop) : ActualSupportersConcrete (oneWorld g) () :=
  fun _ _ _ _ _ => True.intro

theorem rotating_root : RootWithoutUnderived rotating false := by
  refine ⟨⟨false, True.intro, True.intro⟩, ?_, ?_, ⟨false, ⟨⟨True.intro, True.intro⟩, ?_⟩,
    fun _ _ => True.intro⟩, ?_⟩
  · refine wf_of_heightOne _ _ ?_
    intro y x h z hz
    have h1 : y = false := h.1
    have h2 : y = !false := hz.2
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro _ _ _ hc
    obtain ⟨_, _, _, habs⟩ := hc
    exact (habs True.intro).elim
  · intro y hy
    exact Bool.noConfusion (hy.2.2.2 : false = !false)
  · rintro ⟨t, _, _, h⟩
    cases t with
    | false => exact h true true True.intro ⟨rfl, rfl⟩
    | true => exact h false false True.intro ⟨rfl, rfl⟩

theorem possibleContingent_absent : ¬ possibleContingent.ontic.ExistsAt false true :=
  fun h => h.elim Bool.noConfusion Bool.noConfusion

theorem possibleContingent_root : RootWithoutUnderived possibleContingent false := by
  refine ⟨⟨false, True.intro, Or.inl rfl⟩, ?_, ?_, ⟨false, ⟨⟨True.intro, Or.inl rfl⟩, ?_⟩,
    fun _ _ => Or.inl rfl⟩, ?_⟩
  · exact wf_of_noEdge _ _ fun _ _ h => Bool.noConfusion h.1
  · intro x _ hx hc
    obtain ⟨_, v, _, habs⟩ := hc
    cases x with
    | false => exact (habs (Or.inl rfl)).elim
    | true => exact (possibleContingent_absent hx).elim
  · exact fun y hy => Bool.noConfusion hy.2.2.1
  · rintro ⟨t, he, _, h⟩
    cases t with
    | true => exact possibleContingent_absent he
    | false => exact h true true (Or.inr rfl) ⟨rfl, rfl, rfl⟩

theorem abstractSupport_root : RootWithoutUnderived abstractSupport () := by
  refine ⟨⟨.d, rfl, True.intro⟩, ?_, ?_, ⟨.d, ⟨⟨rfl, True.intro⟩, ?_⟩, fun _ _ => True.intro⟩, ?_⟩
  · refine ⟨fun a => ⟨a, fun b hb => ?_⟩⟩
    obtain ⟨y, hy⟩ := b
    have hyx : y = .d := hy.1
    subst hyx
    obtain ⟨z, _⟩ := a
    cases z <;> exact hb.elim
  · intro _ _ _ hc
    obtain ⟨_, _, _, habs⟩ := hc
    exact (habs True.intro).elim
  · intro y hy
    have hyx : y = .d := hy.1
    subst hyx
    exact hy.2.2
  · rintro ⟨t, _, _, h⟩
    cases t with
    | d => exact h () .a True.intro True.intro
    | a => exact h () .b True.intro True.intro
    | b => exact h () .a True.intro True.intro

/-- Support in the limits model: `a` supports `d`. -/
def limitsGrounds : Cell → Cell → Prop
  | .d, .d => False
  | .d, .a => False
  | .d, .b => False
  | .a, .d => True
  | .a, .a => False
  | .a, .b => False
  | .b, .d => False
  | .b, .a => False
  | .b, .b => False

/-- `d` exists only at world `true`; `a` and `b` exist everywhere. All are concrete. -/
def limitsExists : Bool → Cell → Prop
  | v, .d => v = true
  | _, .a => True
  | _, .b => True

/-- The limits profile. -/
def limitsProfile : Profile Bool Cell :=
  prof limitsExists (fun _ => True) (fun _ => limitsGrounds)

theorem limits_d_not_necessary : ¬ NecessaryAt limitsProfile.ontic true .d :=
  fun h => Bool.noConfusion (h false True.intro)

theorem limits_noIntoRoots (y : Cell) {v : Bool} (z : Cell) (hz : z = .a ∨ z = .b) :
    ¬ limitsProfile.grounds v y z := by
  rcases hz with rfl | rfl <;> cases y <;> exact id

theorem limits_clauses (c : Clause) : c.holds limitsProfile true := by
  cases c with
  | inhabited => exact ⟨.a, True.intro, True.intro⟩
  | wellFounded =>
    refine wf_of_heightOne _ _ ?_
    intro y x h z hz
    cases y with
    | d => cases x <;> exact h.elim
    | a => cases z <;> exact hz.elim
    | b => cases x <;> exact h.elim
  | closing =>
    intro x _ _ hc
    obtain ⟨_, v, _, habs⟩ := hc
    cases x with
    | d => exact ⟨.a, True.intro, True.intro, True.intro⟩
    | a => exact (habs True.intro).elim
    | b => exact (habs True.intro).elim
  | present =>
    intro v y x hn hy he
    cases x with
    | d => exact (limits_d_not_necessary hn).elim
    | a => exact (limits_noIntoRoots y .a (Or.inl rfl) he).elim
    | b => exact (limits_noIntoRoots y .b (Or.inr rfl) he).elim
  | concrete => exact fun _ _ _ _ _ => True.intro

theorem limits_root (r : Cell) (hr : r = .a ∨ r = .b) : UnderivedRootAt limitsProfile true r := by
  have he : ∀ v, limitsProfile.ontic.ExistsAt v r := by
    rcases hr with rfl | rfl <;> exact fun _ => True.intro
  exact ⟨⟨⟨True.intro, he true⟩, fun y hy => limits_noIntoRoots y r hr hy.2.2⟩,
    fun v _ => he v, fun _ y _ hg => limits_noIntoRoots y r hr hg⟩

/-- Nothing but `a` reaches `d`, and nothing distinct reaches `a` or `b`. -/
theorem limits_ancestor_root {s t : Cell} (ht : t = .a ∨ t = .b)
    (h : GroundAncestor limitsProfile true s t) : s = t := by
  cases h with
  | refl => rfl
  | tail _ hlast => exact (limits_noIntoRoots _ t ht hlast.2.2).elim

theorem limits_b_not_d : ¬ GroundAncestor limitsProfile true Cell.b Cell.d := by
  intro h
  cases h with
  | tail hprev hlast =>
    rename_i mid
    cases mid with
    | d => exact hlast.2.2
    | a => exact Cell.noConfusion (limits_ancestor_root (Or.inl rfl) hprev)
    | b => exact hlast.2.2

/-- Support in the lifting model: `a` supports `d`, and `d` supports `b`. -/
def liftingGrounds : Cell → Cell → Prop
  | .d, .d => False
  | .d, .a => False
  | .d, .b => True
  | .a, .d => True
  | .a, .a => False
  | .a, .b => False
  | .b, .d => False
  | .b, .a => False
  | .b, .b => False

/-- `a` and `b` exist everywhere and `d` only at world `true`. `a` supports `d`, and `d`
supports `b`: a contingent actual concretum supports a necessary one. -/
def liftingProfile : Profile Bool Cell :=
  prof limitsExists (fun _ => True) (fun _ => liftingGrounds)

theorem lifting_d_absent : ¬ liftingProfile.ontic.ExistsAt false .d := Bool.noConfusion

theorem weakerThanLifting : WeakerThanLifting := by
  have clauses : ∀ c : Clause, c.holds liftingProfile true := by
    intro c
    cases c with
    | inhabited => exact ⟨.a, True.intro, True.intro⟩
    | wellFounded =>
      refine ⟨fun t => ?_⟩
      obtain ⟨t, ht⟩ := t
      have hA : ∀ s, s.1 = Cell.a → Acc (fun a b : {x // ActualConcrete liftingProfile true x} =>
          liftingProfile.grounds true a.1 b.1) s := by
        intro s hs
        refine ⟨_, fun u hu => ?_⟩
        rw [hs] at hu
        obtain ⟨u, _⟩ := u
        cases u <;> exact hu.elim
      have hX : ∀ s, s.1 = Cell.d → Acc (fun a b : {x // ActualConcrete liftingProfile true x} =>
          liftingProfile.grounds true a.1 b.1) s := by
        intro s hs
        refine ⟨_, fun u hu => ?_⟩
        rw [hs] at hu
        obtain ⟨u, hu'⟩ := u
        cases u with
        | a => exact hA _ rfl
        | d => exact hu.elim
        | b => exact hu.elim
      cases t with
      | a => exact hA _ rfl
      | d => exact hX _ rfl
      | b =>
        refine ⟨_, fun u hu => ?_⟩
        obtain ⟨u, _⟩ := u
        cases u with
        | d => exact hX _ rfl
        | a => exact hu.elim
        | b => exact hu.elim
    | closing =>
      intro x _ _ hc
      obtain ⟨_, v, _, habs⟩ := hc
      cases x with
      | d => exact ⟨.a, True.intro, True.intro, True.intro⟩
      | a => exact (habs True.intro).elim
      | b => exact (habs True.intro).elim
    | present =>
      intro v y x _ hy he
      cases y <;> cases x <;> first
        | exact he.elim
        | exact ⟨True.intro, True.intro⟩
        | exact ⟨rfl, True.intro⟩
    | concrete => exact fun _ _ _ _ _ => True.intro
  refine ⟨Bool, Cell, liftingProfile, true, clauses, ?_, ?_⟩
  · intro h
    have hn : NecessaryAt liftingProfile.ontic true Cell.b := fun _ _ => True.intro
    have hde : liftingProfile.ontic.ExistsAt true Cell.d := rfl
    exact lifting_d_absent ((h true .d .b hn hde True.intro).1 false True.intro)
  · refine ⟨.a, True.intro, fun _ _ => True.intro, fun v y _ hg => ?_⟩
    cases y <;> exact hg

theorem everyClauseOmitted : EveryClauseOmitted := by
  intro c
  cases c with
  | inhabited =>
    refine ⟨Unit, Empty, oneWorld (fun _ _ => False), (), ?_, fun ⟨t, _⟩ => t.elim⟩
    intro d hd
    cases d with
    | inhabited => exact (hd rfl).elim
    | wellFounded => exact wf_of_noEdge _ _ fun _ _ h => h
    | closing => exact oneWorld_closing _
    | present => exact oneWorld_present _
    | concrete => exact oneWorld_concrete _
  | wellFounded =>
    refine ⟨Unit, Bool, oneWorld (fun y x => y ≠ x), (), ?_, ?_⟩
    · intro d hd
      cases d with
      | inhabited => exact ⟨true, True.intro, True.intro⟩
      | wellFounded => exact (hd rfl).elim
      | closing => exact oneWorld_closing _
      | present => exact oneWorld_present _
      | concrete => exact oneWorld_concrete _
    · rintro ⟨t, _, _, h⟩
      cases t with
      | false => exact h () true True.intro Bool.noConfusion
      | true => exact h () false True.intro Bool.noConfusion
  | closing =>
    let m : Profile Bool Unit := prof (fun v _ => v = true) (fun _ => True) (fun _ _ _ => False)
    refine ⟨Bool, Unit, m, true, ?_, ?_⟩
    · intro d hd
      cases d with
      | inhabited => exact ⟨(), True.intro, rfl⟩
      | wellFounded => exact wf_of_noEdge _ _ fun _ _ h => h
      | closing => exact (hd rfl).elim
      | present => exact fun _ _ _ _ _ h => h.elim
      | concrete => exact fun _ _ _ _ _ => True.intro
    · rintro ⟨_, _, hn, _⟩
      exact Bool.noConfusion (hn false True.intro)
  | present =>
    obtain ⟨_, hWF, hDep, _, hNo⟩ := rotating_root
    refine ⟨Bool, Bool, rotating, false, ?_, hNo⟩
    intro d hd
    cases d with
    | inhabited => exact ⟨false, True.intro, True.intro⟩
    | wellFounded => exact hWF
    | closing => exact hDep
    | present => exact (hd rfl).elim
    | concrete => exact fun _ _ _ _ _ => True.intro
  | concrete =>
    obtain ⟨hPop, hWF, hDep, _, hNo⟩ := abstractSupport_root
    refine ⟨Unit, Cell, abstractSupport, (), ?_, hNo⟩
    intro d hd
    cases d with
    | inhabited => exact hPop
    | wellFounded => exact hWF
    | closing => exact hDep
    | present => exact fun _ _ _ _ _ he => ⟨True.intro, he⟩
    | concrete => exact (hd rfl).elim

theorem endlessDescentOmission : EndlessDescentOmission := by
  refine ⟨oneWorld (fun y x => y = x + 1), ?_, ?_, ?_⟩
  · intro d hd
    cases d with
    | inhabited => exact ⟨0, True.intro, True.intro⟩
    | wellFounded => exact (hd rfl).elim
    | closing => exact oneWorld_closing _
    | present => exact oneWorld_present _
    | concrete => exact oneWorld_concrete _
  · rintro ⟨t, _, _, h⟩
    exact h () (t + 1) True.intro rfl
  · intro y x h
    have h' : y = x + 1 := h
    rw [h']
    exact Nat.lt_succ_self x

theorem rotatingSupport : RotatingSupport := by
  refine ⟨rotating_root, fun _ _ _ _ _ => True.intro, fun _ _ _ _ _ _ => fun _ _ => True.intro, ?_⟩
  intro h
  have := (h true true false (fun _ _ => True.intro) (fun _ _ => True.intro) True.intro
    ⟨rfl, rfl⟩).1
  exact Bool.noConfusion this

theorem possibleContingentSupport : PossibleContingentSupport := by
  refine ⟨possibleContingent_root, fun _ _ _ _ _ => True.intro, ?_, ?_⟩
  · intro v y _ hy _ _ hg
    have hyt : y = true := hg.2.1
    subst hyt
    exact (possibleContingent_absent (hy false True.intro)).elim
  · intro h
    have hn := h true true false (Or.inr rfl) (fun _ _ => Or.inl rfl) ⟨rfl, rfl, rfl⟩
    exact possibleContingent_absent (hn false True.intro)

theorem abstractSupportControl : AbstractSupport := by
  refine ⟨abstractSupport_root, fun _ _ _ _ _ he => ⟨True.intro, he⟩,
    fun _ _ _ _ _ he => ⟨fun _ _ => True.intro, True.intro, he⟩, ?_⟩
  intro h
  exact Cell.noConfusion (h .a .d ⟨rfl, True.intro⟩ True.intro True.intro)

theorem groundLimits : GroundLimits := by
  refine ⟨Bool, Cell, limitsProfile, true, limits_clauses, .a, .b, .d, false, Cell.noConfusion,
    limits_root _ (Or.inl rfl), limits_root _ (Or.inr rfl), ?_, ?_,
    ⟨True.intro, True.intro, True.intro⟩, limits_b_not_d, True.intro, True.intro,
    Bool.noConfusion, rfl⟩
  · exact fun h => Cell.noConfusion (limits_ancestor_root (Or.inr rfl) h)
  · exact fun h => Cell.noConfusion (limits_ancestor_root (Or.inl rfl) h)

theorem underivedRouteControls : UnderivedRouteControls :=
  ⟨fun _ _ m w hWF hDep hEM hP hC => everyConcretumDescends m w hWF hDep hEM hP hC,
    fun _ _ m w h => presentOfLifting m w h, everyClauseOmitted, endlessDescentOmission,
    rotatingSupport, possibleContingentSupport, abstractSupportControl, weakerThanLifting,
    groundLimits⟩

end TruthCore.Causality.UnderivedRootRoute
