import TruthCore.Causality.CogitoNecessaryConcrete

/-!
# Well-founded actual ancestry: necessary concretum or nonnecessary root (#553)

Source-free and stipulative: nothing here is attributed to any author, and
nothing shows that any horn is actual or metaphysically possible.

Reused unchanged: the #505 `Profile`, `InhabitedAt`, `NecessaryConcreteAt`,
the #536 `InhabitedConcreteAt` (the hypothesis that the Cogito results supply),
`EveryContingentGroundedAt`, and the #564 `ActualConcreteGround`. A root is a
root of the profile's selected relation `grounds w` only: it may have a
non-concrete or unmodelled explanation (`DEF-BRUTE-ROOT-RELATIVE-GROUNDING`).

What this adds to `BRUTE-ROOT-DISJUNCTION` and `COGITO-ANCESTRY-ROOT-FORK`:

* `ActualGroundingWF` restricts well-foundedness to actual concreta. Whole-carrier
  well-foundedness implies it, and it holds in an inhabited model where the
  whole-carrier condition fails;
* the second horn says *nonnecessary* (`¬ NecessaryAt`), kept apart from
  *contingent* (`ContingentAt`, a witnessed accessible absence);
* #553 conjectured that the root theorem is constructive. It is not: its
  reductio form `¬¬ NonnecessaryRootAt` needs no excluded middle, but the theorem
  with an existential conclusion, quantified over profiles, implies
  `ExcludedMiddle` (`RootPrincipleImpliesExcludedMiddle`). Excluded middle is an
  explicit hypothesis here, never a Lean axiom;
* the horns are not exclusive (`NecessaryRootOverlapModel`,
  `NecessaryCycleOverlapModel`), and each is witnessed;
* the premise closing the root horn, `EveryContingentGroundedAt`, is, with
  excluded middle, equivalent to the denial of a contingent root. So adding it
  rejects the horn; it needs its own defence.

`NecessaryAt` is accessibility-relative and de re over rigid candidate identity.
-/
namespace TruthCore.Causality.NecessaryRootFork

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- `x` is concrete and exists at `w`. -/
def ActualConcrete (m : Profile W B) (w : W) (x : B) : Prop :=
  m.concrete x ∧ m.ontic.ExistsAt w x

/-- `grounds w` restricted to actual concreta is well-founded. Cycles and
descending chains through absent or non-concrete candidates are unconstrained. -/
def ActualGroundingWF (m : Profile W B) (w : W) : Prop :=
  WellFounded fun a b : {x // ActualConcrete m w x} => m.grounds w a.1 b.1

/-- `x` is an actual concretum with no actual concrete ground at `w`. It may
have an abstract, absent or unmodelled ground or explanation. -/
def ActualRoot (m : Profile W B) (w : W) (x : B) : Prop :=
  ActualConcrete m w x ∧ ∀ y, ¬ ActualConcreteGround m w y x

/-- Some actual root does not exist at every world accessible from `w`. A
negated universal: no absent-at world is thereby exhibited. -/
def NonnecessaryRootAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, ActualRoot m w x ∧ ¬ NecessaryAt m.ontic w x

/-- Some actual root is contingent at `w`: an accessible world lacking it is
exhibited. -/
def ContingentRootAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, ActualRoot m w x ∧ ContingentAt m.ontic w x

/-- The two-horned fork. The horns are not exclusive. -/
def NecessaryOrNonnecessaryRoot (m : Profile W B) (w : W) : Prop :=
  NecessaryConcreteAt m w ∨ NonnecessaryRootAt m w

/-- The three-horned fork: a necessary concretum; or well-founded actual
grounding with a nonnecessary root; or non-well-founded actual grounding. Only
the second and third horns exclude each other. -/
def NecessaryRootTrilemma (m : Profile W B) (w : W) : Prop :=
  NecessaryConcreteAt m w ∨ (ActualGroundingWF m w ∧ NonnecessaryRootAt m w) ∨
    ¬ ActualGroundingWF m w

/-- The same profile with `Ontic.Causes` as its selected relation. Everything
above then speaks of roots of causing rather than of grounding. -/
def withCauses (m : Profile W B) : Profile W B :=
  { m with grounds := m.ontic.Causes }

/-! ## Descent -/

/-- An inhabited world with well-founded actual grounding has an actual root. -/
theorem actualRootExists (m : Profile W B) (w : W) (hEM : ExcludedMiddle)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w) :
    ∃ x, ActualRoot m w x := by
  obtain ⟨x, hc, he⟩ := hPop
  have walk : ∀ a : {x // ActualConcrete m w x}, ∃ x, ActualRoot m w x := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      rcases hEM (∃ y, ActualConcreteGround m w y a.1) with ⟨y, hy⟩ | hnone
      · exact ih ⟨y, hy.1, hy.2.1⟩ hy.2.2
      · exact ⟨a.1, a.2, fun y hy => hnone ⟨y, hy⟩⟩
  exact walk ⟨x, hc, he⟩

/-- Constructive core: no hypothesis of excluded middle. Under inhabitedness and
well-founded actual grounding, denying both a necessary concretum and a
nonnecessary root is absurd. -/
theorem notNotNonnecessaryRoot (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hNoNec : ¬ NecessaryConcreteAt m w) :
    ¬¬ NonnecessaryRootAt m w := by
  intro hNone
  obtain ⟨x, hc, he⟩ := hPop
  have walk : ∀ a : {x // ActualConcrete m w x}, False := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      refine hNone ⟨a.1, ⟨a.2, fun y hy => ih ⟨y, hy.1, hy.2.1⟩ hy.2.2⟩, ?_⟩
      exact fun hn => hNoNec ⟨a.1, a.2.1, a.2.2, hn⟩
  exact walk ⟨x, hc, he⟩

/-- The coverage theorem. Compare `contingentBruteRootOfNoNecessary`, which has
whole-carrier well-foundedness and a contingent root. -/
theorem necessaryOrNonnecessaryRoot (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w) (hEM : ExcludedMiddle) :
    NecessaryOrNonnecessaryRoot m w := by
  obtain ⟨x, hr⟩ := actualRootExists m w hEM hPop hWF
  rcases hEM (NecessaryAt m.ontic w x) with hn | hn
  · exact Or.inl ⟨x, hr.1.1, hr.1.2, hn⟩
  · exact Or.inr ⟨x, hr, hn⟩

/-- The three-horned coverage theorem. -/
theorem necessaryRootTrilemma (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hEM : ExcludedMiddle) :
    NecessaryRootTrilemma m w := by
  rcases hEM (ActualGroundingWF m w) with hWF | hWF
  · rcases necessaryOrNonnecessaryRoot m w hPop hWF hEM with hn | hr
    · exact Or.inl hn
    · exact Or.inr (Or.inl ⟨hWF, hr⟩)
  · exact Or.inr (Or.inr hWF)

/-- The fork for roots of `Ontic.Causes`: `necessaryOrNonnecessaryRoot` at
`withCauses m`. Its necessary horn is unaffected by the choice of relation. -/
theorem causalNecessaryOrNonnecessaryRoot (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF (withCauses m) w)
    (hEM : ExcludedMiddle) :
    NecessaryOrNonnecessaryRoot (withCauses m) w :=
  necessaryOrNonnecessaryRoot (withCauses m) w hPop hWF hEM

/-- With excluded middle, an existing nonnecessary individual is contingent. -/
theorem contingentRootOfNonnecessary (m : Profile W B) (w : W) (hEM : ExcludedMiddle)
    (h : NonnecessaryRootAt m w) : ContingentRootAt m w := by
  obtain ⟨x, hr, hn⟩ := h
  refine ⟨x, hr, hr.1.2, ?_⟩
  rcases hEM (∃ v, m.ontic.frame.access w v ∧ ¬ m.ontic.ExistsAt v x) with hv | hv
  · exact hv
  · refine (hn fun v hac => ?_).elim
    rcases hEM (m.ontic.ExistsAt v x) with he | he
    · exact he
    · exact (hv ⟨v, hac, he⟩).elim

/-- Conversely, and with no excluded middle, a contingent root is nonnecessary. -/
theorem nonnecessaryRootOfContingent (m : Profile W B) (w : W)
    (h : ContingentRootAt m w) : NonnecessaryRootAt m w := by
  obtain ⟨x, hr, _, v, hv, habs⟩ := h
  exact ⟨x, hr, fun hn => habs (hn v hv)⟩

/-! ## Closing the root horn -/

/-- The premise closing the root horn is, with excluded middle, the denial of a
contingent root. -/
theorem everyContingentGrounded_iff_noContingentRoot (m : Profile W B) (w : W)
    (hEM : ExcludedMiddle) :
    EveryContingentGroundedAt m w ↔ ¬ ContingentRootAt m w := by
  constructor
  · intro hG ⟨x, hr, hcont⟩
    obtain ⟨y, hyc, hye, hyg⟩ := hG x hr.1.1 hr.1.2 hcont
    exact hr.2 y ⟨hyc, hye, hyg⟩
  · intro hNo x hc he hcont
    rcases hEM (∃ y, m.concrete y ∧ m.ontic.ExistsAt w y ∧ m.grounds w y x) with hy | hy
    · exact hy
    · exact (hNo ⟨x, ⟨⟨hc, he⟩, fun y hg => hy ⟨y, hg⟩⟩, hcont⟩).elim

/-- Inhabitedness, well-founded actual grounding and the anti-brute-root premise
give a necessary concretum. `necessaryConcreteOfGroundedContingents` has
whole-carrier well-foundedness and uses Lean's classical axioms. -/
theorem necessaryConcreteOfActualGrounded (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w) (hWF : ActualGroundingWF m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  rcases necessaryOrNonnecessaryRoot m w hPop hWF hEM with hn | hr
  · exact hn
  · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
      (contingentRootOfNonnecessary m w hEM hr)).elim

/-! ## Excluded middle cannot be removed from the existential form -/

/-- #553's target, quantified over all profiles: inhabited, well-founded actual
grounding and no necessary concretum give a nonnecessary root. -/
def RootPrinciple : Prop :=
  ∀ (W B : Type) (m : Profile W B) (w : W),
    InhabitedAt m w → ActualGroundingWF m w → ¬ NecessaryConcreteAt m w →
      NonnecessaryRootAt m w

/-- `RootPrinciple` holds given excluded middle, and it implies excluded middle.
Lean checks this with no classical axiom; so the principle has no constructive
proof unless excluded middle has one. -/
def RootPrincipleImpliesExcludedMiddle : Prop :=
  (ExcludedMiddle → RootPrinciple) ∧ (RootPrinciple → ExcludedMiddle)

/-- Two candidates. `true` is an actual concretum; `false` is one exactly if `p`,
and then it grounds `true`. A root of this profile at world `true` decides `p`.
Each candidate is absent at world `false`, so no candidate is necessary. -/
def decidingProfile (p : Prop) : Profile Bool Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => w = true ∧ (x = true ∨ p)
    Causes := fun _ _ _ => False
  }
  concrete := fun _ => True
  grounds := fun _ y x => y = false ∧ x = true

theorem decidingWF (p : Prop) : ActualGroundingWF (decidingProfile p) true := by
  have hFalse : ∀ a : {x // ActualConcrete (decidingProfile p) true x}, a.1 = false →
      Acc (fun a b : {x // ActualConcrete (decidingProfile p) true x} =>
        (decidingProfile p).grounds true a.1 b.1) a := by
    intro a ha
    refine Acc.intro a fun b hb => ?_
    have : a.1 = true := hb.2
    rw [ha] at this
    cases this
  refine ⟨fun a => ?_⟩
  obtain ⟨x, hx⟩ := a
  cases x with
  | false => exact hFalse ⟨false, hx⟩ rfl
  | true =>
      refine Acc.intro _ fun b hb => hFalse b hb.1

theorem rootPrincipleImpliesExcludedMiddle : RootPrinciple → ExcludedMiddle := by
  intro h p
  have hPop : InhabitedAt (decidingProfile p) true :=
    ⟨true, True.intro, rfl, Or.inl rfl⟩
  have hNoNec : ¬ NecessaryConcreteAt (decidingProfile p) true := by
    intro ⟨_, _, _, hn⟩
    have : false = true := (hn false True.intro).1
    cases this
  obtain ⟨x, hr, _⟩ := h Bool Bool (decidingProfile p) true hPop (decidingWF p) hNoNec
  cases x with
  | false =>
      obtain ⟨_, _, hor⟩ := hr.1
      rcases hor with h | hp
      · cases h
      · exact Or.inl hp
  | true =>
      refine Or.inr fun hp => hr.2 false ⟨True.intro, ⟨rfl, Or.inr hp⟩, rfl, rfl⟩

/-! ## Witnesses and controls

All are logical models over universal or stated frames; none is claimed
metaphysically possible. -/

/-- One candidate existing at every world, with no grounds. -/
def necessaryProfile : Profile Bool Unit :=
  { ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ _ _ => False }

/-- `ActualGroundingWF` holds whenever `grounds w` has no edge at all. -/
theorem wf_of_noEdge (m : Profile W B) (w : W) (h : ∀ y x, ¬ m.grounds w y x) :
    ActualGroundingWF m w :=
  ⟨fun a => Acc.intro a fun _ hb => (h _ _ hb).elim⟩

/-- Necessary horn: inhabited, well-founded, a necessary concretum, and no
nonnecessary root. Omitting "no necessary concretum" from the root principle. -/
def NecessaryHornModel : Prop :=
  InhabitedAt necessaryProfile true ∧ ActualGroundingWF necessaryProfile true ∧
    NecessaryConcreteAt necessaryProfile true ∧ ¬ NonnecessaryRootAt necessaryProfile true

/-- Root horn, reusing `bruteProfile`: inhabited, well-founded, no necessary
concretum, and a contingent, hence nonnecessary, root. -/
def RootHornModel : Prop :=
  InhabitedAt bruteProfile true ∧ ActualGroundingWF bruteProfile true ∧
    ¬ NecessaryConcreteAt bruteProfile true ∧ ContingentRootAt bruteProfile true ∧
    NonnecessaryRootAt bruteProfile true

/-- Cycle variant of the third horn, reusing `cycleProfile`: inhabited, not
well-founded, no necessary concretum, no nonnecessary root. Omitting
well-foundedness from the root principle. -/
def CycleHornModel : Prop :=
  InhabitedAt cycleProfile true ∧ ¬ ActualGroundingWF cycleProfile true ∧
    ¬ NecessaryConcreteAt cycleProfile true ∧ ¬ NonnecessaryRootAt cycleProfile true

/-- Natural-number candidates existing only at world `true`, each grounded by
its successor. -/
def chainProfile : Profile Bool Nat :=
  { ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = true, Causes := fun _ y x => y = x + 1 }
    concrete := fun _ => True
    grounds := fun _ y x => y = x + 1 }

/-- Chain variant of the third horn: not well-founded, no individual grounds
itself through any finite chain, no necessary concretum, no nonnecessary root.
So non-well-foundedness does not imply a cycle. The chain is an order of
candidates, not a completed temporal process. -/
def ChainHornModel : Prop :=
  InhabitedAt chainProfile true ∧ ¬ ActualGroundingWF chainProfile true ∧
    (∀ x, ¬ Relation.TransGen (chainProfile.grounds true) x x) ∧
    ¬ NecessaryConcreteAt chainProfile true ∧ ¬ NonnecessaryRootAt chainProfile true

/-- Inhabitedness omitted, reusing `unitProfile`: no actual concretum; well-founded,
no necessary concretum, no nonnecessary root. -/
def EmptyControl : Prop :=
  ¬ InhabitedAt (unitProfile False True) () ∧
    ActualGroundingWF (unitProfile False True) () ∧
    ¬ NecessaryConcreteAt (unitProfile False True) () ∧
    ¬ NonnecessaryRootAt (unitProfile False True) ()

/-- `true` exists at both worlds, `false` only at world `true`; no grounds. -/
def overlapProfile : Profile Bool Bool :=
  { ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w x => x = true ∨ w = true, Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ _ _ => False }

/-- The first two horns together: well-founded, with a necessary concretum and a
nonnecessary root, while `EveryContingentGroundedAt` fails. So a necessary
concretum with well-founded actual grounding does not imply that premise. -/
def NecessaryRootOverlapModel : Prop :=
  ActualGroundingWF overlapProfile true ∧ NecessaryConcreteAt overlapProfile true ∧
    NonnecessaryRootAt overlapProfile true ∧ ¬ EveryContingentGroundedAt overlapProfile true

/-- The first and third horns together, reusing `strictProfile`. -/
def NecessaryCycleOverlapModel : Prop :=
  NecessaryConcreteAt strictProfile true ∧ ¬ ActualGroundingWF strictProfile true

/-- Restriction is weaker: whole-carrier well-foundedness implies
`ActualGroundingWF`, and at world `false` of `strictProfile` the latter holds
with the former failing, in an inhabited world. -/
def RestrictedWeakerControl : Prop :=
  (∀ (W B : Type) (m : Profile W B) (w : W),
    WellFounded (m.grounds w) → ActualGroundingWF m w) ∧
    InhabitedAt strictProfile false ∧ ActualGroundingWF strictProfile false ∧
    ¬ WellFounded (strictProfile.grounds false)

/-- `true` grounds `false` while `false` causes `true`; both exist only at world
`true`. -/
def relationProfile : Profile Bool Bool :=
  { ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun w _ => w = true, Causes := fun _ y x => y = false ∧ x = true }
    concrete := fun _ => True
    grounds := fun _ y x => y = true ∧ x = false }

/-- A grounding root need not be a causal root, nor conversely: in one model
`true` is a root of grounding only and `false` of causing only. -/
def RelationTypeControl : Prop :=
  ActualRoot relationProfile true true ∧ ¬ ActualRoot relationProfile true false ∧
    ActualRoot (withCauses relationProfile) true false ∧
    ¬ ActualRoot (withCauses relationProfile) true true

/-- Some actual concretum has, at every accessible world, an existing counterpart
under `Cp`, where `Cp` is any supplied relation on candidates. -/
def CounterpartPersistsAt (m : Profile W B) (Cp : B → B → Prop) (w : W) : Prop :=
  ∃ x, ActualConcrete m w x ∧ ∀ v, m.ontic.frame.access w v →
    ∃ y, Cp x y ∧ m.ontic.ExistsAt v y

/-- Counterpart persistence does not give rigid necessity: in `boundaryRival`,
under sameness of rank, a counterpart exists at each world, and no candidate is
necessary. -/
def CounterpartControl : Prop :=
  CounterpartPersistsAt boundaryRival (fun x y => x.2 = y.2) false ∧
    ¬ NecessaryConcreteAt boundaryRival false

/-- One candidate existing only at world `true`, in a frame with no accessibility. -/
def noAccessProfile : Profile Bool Unit :=
  { ontic := { frame := ⟨fun _ _ => False⟩, ExistsAt := fun w _ => w = true, Causes := fun _ _ _ => False }
    concrete := fun _ => True
    grounds := fun _ _ _ => False }

/-- The necessary horn is accessibility-relative: with no accessible world a
candidate absent at world `false` satisfies it. -/
def AccessibilityControl : Prop :=
  NecessaryConcreteAt noAccessProfile true ∧ ¬ noAccessProfile.ontic.ExistsAt false ()

/-- The control bundle. The conjuncts are, in order: the necessary, root, cycle
and chain branch witnesses (the first, third and `EmptyControl` being the three
omission controls of the root principle); the two overlaps; the restriction,
relation-type, counterpart and accessibility controls; the reduction of excluded
middle to the root principle; and, for every profile and world, the constructive
reductio form of the root principle. -/
def NecessaryRootControls : Prop :=
  NecessaryHornModel ∧ RootHornModel ∧ CycleHornModel ∧ ChainHornModel ∧ EmptyControl ∧
    NecessaryRootOverlapModel ∧ NecessaryCycleOverlapModel ∧
    RestrictedWeakerControl ∧ RelationTypeControl ∧ CounterpartControl ∧ AccessibilityControl ∧
    RootPrincipleImpliesExcludedMiddle ∧
    (∀ (W B : Type) (m : Profile W B) (w : W),
      InhabitedAt m w → ActualGroundingWF m w → ¬ NecessaryConcreteAt m w →
        ¬¬ NonnecessaryRootAt m w)

/-! ## Proofs of the controls -/

theorem necessaryHornModel : NecessaryHornModel :=
  ⟨⟨(), True.intro, True.intro⟩, wf_of_noEdge _ _ fun _ _ h => h,
    ⟨(), True.intro, True.intro, fun _ _ => True.intro⟩,
    fun ⟨_, _, hn⟩ => hn fun _ _ => True.intro⟩

theorem rootHornModel : RootHornModel := by
  have hr : ContingentRootAt bruteProfile true :=
    ⟨(), ⟨⟨True.intro, rfl⟩, fun _ hy => hy.2.2⟩, rfl, false, True.intro, fun h => by cases h⟩
  refine ⟨⟨(), True.intro, rfl⟩, wf_of_noEdge _ _ fun _ _ h => h, ?_, hr,
    nonnecessaryRootOfContingent _ _ hr⟩
  intro ⟨_, _, _, hn⟩
  cases (hn false True.intro : false = true)

/-- Non-well-foundedness of the restricted relation from a self-predecessor set. -/
theorem not_wf_of_descent (m : Profile W B) (w : W) (S : B → Prop)
    (hAct : ∀ x, S x → ActualConcrete m w x)
    (hStep : ∀ x, S x → ∃ y, S y ∧ m.grounds w y x)
    (x₀ : B) (h₀ : S x₀) : ¬ ActualGroundingWF m w := by
  intro hWF
  have walk : ∀ a : {x // ActualConcrete m w x}, S a.1 → False := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      intro hs
      obtain ⟨y, hy, hg⟩ := hStep a.1 hs
      exact ih ⟨y, hAct y hy⟩ hg hy
  exact walk ⟨x₀, hAct x₀ h₀⟩ h₀

theorem boolNeTrueFalse : ∀ x : Bool, ∃ y : Bool, y ≠ x := by
  intro x
  cases x with
  | false => exact ⟨true, fun h => by cases h⟩
  | true => exact ⟨false, fun h => by cases h⟩

theorem cycleHornModel : CycleHornModel := by
  refine ⟨⟨true, True.intro, rfl⟩, ?_, ?_, ?_⟩
  · exact not_wf_of_descent cycleProfile true (fun _ => True)
      (fun _ _ => ⟨True.intro, rfl⟩)
      (fun x _ => let ⟨y, hy⟩ := boolNeTrueFalse x; ⟨y, True.intro, hy⟩) true True.intro
  · intro ⟨_, _, _, hn⟩
    cases (hn false True.intro : false = true)
  · intro ⟨x, hr, _⟩
    obtain ⟨y, hy⟩ := boolNeTrueFalse x
    exact hr.2 y ⟨True.intro, rfl, hy⟩

theorem chain_lt {x y : Nat} (h : Relation.TransGen (chainProfile.grounds true) y x) : x < y := by
  induction h with
  | single hb =>
      have hb' : _ = _ + 1 := hb
      rw [hb']
      exact Nat.lt_succ_self _
  | tail _ hc ih =>
      have hc' : _ = _ + 1 := hc
      rw [hc'] at ih
      exact Nat.lt_trans (Nat.lt_succ_self _) ih

theorem chainHornModel : ChainHornModel := by
  refine ⟨⟨0, True.intro, rfl⟩, ?_, fun x h => Nat.lt_irrefl x (chain_lt h), ?_, ?_⟩
  · exact not_wf_of_descent chainProfile true (fun _ => True)
      (fun _ _ => ⟨True.intro, rfl⟩) (fun x _ => ⟨x + 1, True.intro, rfl⟩) 0 True.intro
  · intro ⟨_, _, _, hn⟩
    cases (hn false True.intro : false = true)
  · intro ⟨x, hr, _⟩
    exact hr.2 (x + 1) ⟨True.intro, rfl, rfl⟩

theorem emptyControl : EmptyControl :=
  ⟨fun ⟨_, _, h⟩ => h, wf_of_noEdge _ _ fun _ _ h => h, fun ⟨_, _, h, _⟩ => h,
    fun ⟨_, hr, _⟩ => hr.1.2⟩

theorem necessaryRootOverlapModel : NecessaryRootOverlapModel := by
  have hAbsent : ¬ overlapProfile.ontic.ExistsAt false false := by
    intro h
    rcases h with h | h <;> cases h
  have hRootFalse : ActualRoot overlapProfile true false :=
    ⟨⟨True.intro, Or.inr rfl⟩, fun _ hy => hy.2.2⟩
  refine ⟨wf_of_noEdge _ _ fun _ _ h => h,
    ⟨true, True.intro, Or.inl rfl, fun _ _ => Or.inl rfl⟩,
    ⟨false, hRootFalse, fun hn => hAbsent (hn false True.intro)⟩, ?_⟩
  intro hG
  obtain ⟨_, _, _, h⟩ := hG false True.intro (Or.inr rfl) ⟨Or.inr rfl, false, True.intro, hAbsent⟩
  exact h

theorem necessaryCycleOverlapModel : NecessaryCycleOverlapModel := by
  refine ⟨⟨Cand.thinker, True.intro, True.intro, fun _ _ => True.intro⟩, ?_⟩
  refine not_wf_of_descent strictProfile true
    (fun x => x = Cand.left ∨ x = Cand.right) ?_ ?_ Cand.left (Or.inl rfl)
  · intro x hx
    rcases hx with rfl | rfl <;> exact ⟨True.intro, rfl⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨Cand.right, Or.inr rfl, True.intro⟩
    · exact ⟨Cand.left, Or.inl rfl, True.intro⟩

theorem restrictedWeakerControl : RestrictedWeakerControl := by
  refine ⟨fun _ _ m w h => InvImage.wf Subtype.val h, ⟨Cand.thinker, True.intro, True.intro⟩, ?_, ?_⟩
  · have hAct : ∀ a : {x // ActualConcrete strictProfile false x}, a.1 = Cand.thinker := by
      intro ⟨x, _, he⟩
      cases x with
      | thinker => rfl
      | left => cases (he : false = true)
      | right => cases (he : false = true)
      | brute => cases (he : false = true)
    refine ⟨fun a => Acc.intro a fun b hb => ?_⟩
    have : strictProfile.grounds false b.1 a.1 := hb
    rw [hAct a] at this
    cases hb' : b.1 <;> rw [hb'] at this <;> exact this.elim
  · intro hWF
    have walk : ∀ x : Cand, (x = Cand.left ∨ x = Cand.right) → False := by
      intro x
      induction x using hWF.induction with
      | _ x ih =>
        intro hx
        rcases hx with rfl | rfl
        · exact ih Cand.right True.intro (Or.inr rfl)
        · exact ih Cand.left True.intro (Or.inl rfl)
    exact walk Cand.left (Or.inl rfl)

theorem relationTypeControl : RelationTypeControl := by
  refine ⟨⟨⟨True.intro, rfl⟩, ?_⟩, fun h => h.2 true ⟨True.intro, rfl, rfl, rfl⟩,
    ⟨⟨True.intro, rfl⟩, ?_⟩, fun h => h.2 false ⟨True.intro, rfl, rfl, rfl⟩⟩
  · intro _ hy
    cases (hy.2.2.2 : true = false)
  · intro _ hy
    cases (hy.2.2.2 : false = true)

theorem counterpartControl : CounterpartControl := by
  refine ⟨⟨(false, false), ⟨True.intro, rfl⟩, fun v _ => ⟨(v, false), rfl, rfl⟩⟩, ?_⟩
  exact boundaryRivalNoNecessary

theorem accessibilityControl : AccessibilityControl :=
  ⟨⟨(), True.intro, rfl, fun _ h => h.elim⟩, fun h => by cases (h : false = true)⟩

theorem rootPrincipleEquivEM : RootPrincipleImpliesExcludedMiddle := by
  refine ⟨fun hEM W B m w hPop hWF hNoNec => ?_, rootPrincipleImpliesExcludedMiddle⟩
  rcases necessaryOrNonnecessaryRoot m w hPop hWF hEM with hn | hr
  · exact (hNoNec hn).elim
  · exact hr

theorem necessaryRootControls : NecessaryRootControls :=
  ⟨necessaryHornModel, rootHornModel, cycleHornModel, chainHornModel, emptyControl,
    necessaryRootOverlapModel, necessaryCycleOverlapModel, restrictedWeakerControl,
    relationTypeControl, counterpartControl, accessibilityControl, rootPrincipleEquivEM,
    fun _ _ m w hPop hWF hNoNec => notNotNonnecessaryRoot m w hPop hWF hNoNec⟩

end TruthCore.Causality.NecessaryRootFork
