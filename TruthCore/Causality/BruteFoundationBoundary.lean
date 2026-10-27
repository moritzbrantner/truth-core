import TruthCore.German.Kant.CosmologicalInference

/-!
# A contingent brute root survives a boundary-exception causal law

Analyst-defined models for #505 and #487, not source attributions.

The positive result needs every actual *contingent concrete being* to have an
actual concrete predecessor, plus well-foundedness of that predecessor
relation. The rival model has nonempty concrete inventories in BOTH worlds,
and every noninitial individual has a distinct existing cause. Nevertheless
its two initial roots are contingent and uncaused. It therefore invalidates
the attempted inference from a boundary-exception causal law to a necessarily
existing concrete individual.

Worlds stand for complete alternative histories, not successive instants.
The predecessor relation is read as existential grounding for this test; it
is not automatically efficient causation of a temporally first event.
-/ 

namespace TruthCore.Causality.BruteFoundationBoundary

open TruthCore.German.Kant.CosmologicalInference

/-- Concrete existence, with a world-relative grounding relation. The carrier
contains candidate individuals, including those absent from a given world.
No explanatory completeness, PSR, or divine attribute is built in. -/
structure Profile (World Being : Type) where
  ontic : Ontic World Being
  concrete : Being → Prop
  grounds : World → Being → Being → Prop

/-- There is at least one actual concrete individual. -/
def InhabitedAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, m.concrete x ∧ m.ontic.ExistsAt w x

/-- At least one and the SAME concrete individual exists actually and in
all worlds accessible from w. This is de re relative to rigid candidate identity. -/
def NecessaryConcreteAt (m : Profile W B) (w : W) : Prop :=
  ∃ x, m.concrete x ∧ m.ontic.ExistsAt w x ∧ NecessaryAt m.ontic w x

/-- Every actual contingent concrete individual has an actually existing
concrete predecessor. This is stronger than 'every noninitial event has a
cause' and stronger than a PSR allowing non-concrete explanations. -/
def EveryContingentGroundedAt (m : Profile W B) (w : W) : Prop :=
  ∀ x, m.concrete x → m.ontic.ExistsAt w x →
    ContingentAt m.ontic w x →
      ∃ y, m.concrete y ∧ m.ontic.ExistsAt w y ∧ m.grounds w y x

/-- Conditional necessary-concrete existence. The proof walks down a
well-founded actual grounding relation: a minimal actual concrete being
cannot be contingent if every contingent being has a predecessor.

This does not prove that real existential grounding is well-founded or that
the contingent-dependence rule is true. -/
theorem necessaryConcreteOfGroundedContingents
    (m : Profile W B) (w : W)
    (hPop : InhabitedAt m w)
    (hWF : WellFounded (m.grounds w))
    (hDep : EveryContingentGroundedAt m w) :
    NecessaryConcreteAt m w := by
  have walk : ∀ x : B, m.concrete x → m.ontic.ExistsAt w x →
      NecessaryConcreteAt m w := by
    intro x
    induction x using hWF.induction with
    | h x ih =>
      intro hc he
      by_cases hCont : ContingentAt m.ontic w x
      · rcases hDep x hc he hCont with ⟨y, hyConcrete, hyExists, hyGrounds⟩
        exact ih y hyGrounds hyConcrete hyExists
      · refine ⟨x, hc, he, ?_⟩
        intro v hv
        by_cases hExists : m.ontic.ExistsAt v x
        · exact hExists
        · exact False.elim (hCont ⟨he, ⟨v, hv, hExists⟩⟩)
  rcases hPop with ⟨x, hc, he⟩
  exact walk x hc he

/-- The exact four-premise contradictory configuration: an inhabited actual
world; a well-founded grounding relation; all contingent concrete existents
grounded; and every actual concrete individual contingent. -/
theorem noAllContingentGroundedWellFounded
    (m : Profile W B) (w : W)
    (hPop : InhabitedAt m w)
    (hWF : WellFounded (m.grounds w))
    (hDep : EveryContingentGroundedAt m w)
    (hAllContingent : ∀ x, m.concrete x → m.ontic.ExistsAt w x →
      ContingentAt m.ontic w x) : False := by
  rcases necessaryConcreteOfGroundedContingents m w hPop hWF hDep with
    ⟨x, hc, he, hNecessary⟩
  rcases hAllContingent x hc he with ⟨_, v, hv, hAbsent⟩
  exact hAbsent (hNecessary v hv)

/-- A stronger *disjunctive elimination*: in any inhabited world with a
well-founded existential-grounding relation, failure of de re necessary
concrete existence forces an **actual contingent concrete root**.

The root has no incoming ground from another actual concrete individual.
This does not rule out a non-concrete explanatory reason, and it does not
supply metaphysical evidence that the no-necessary-being hypothesis is true.

Proof uses classical case analysis on contingency and on the existence of
a predecessor; this is a result in ordinary classical logic. -/
theorem contingentBruteRootOfNoNecessary
    (m : Profile W B) (w : W)
    (hPop : InhabitedAt m w)
    (hWF : WellFounded (m.grounds w))
    (hNoNecessary : ¬ NecessaryConcreteAt m w) :
    ∃ root, m.concrete root ∧ m.ontic.ExistsAt w root ∧
      ContingentAt m.ontic w root ∧
      (∀ y, m.concrete y → m.ontic.ExistsAt w y →
        ¬ m.grounds w y root) := by
  classical
  have findRoot : ∀ x : B, m.concrete x → m.ontic.ExistsAt w x →
      ∃ root, m.concrete root ∧ m.ontic.ExistsAt w root ∧
        (∀ y, m.concrete y → m.ontic.ExistsAt w y →
          ¬ m.grounds w y root) := by
    intro x
    induction x using hWF.induction with
    | h x ih =>
      intro hxConcrete hxExists
      by_cases hp : ∃ y, m.concrete y ∧
          m.ontic.ExistsAt w y ∧ m.grounds w y x
      · rcases hp with ⟨y, hyConcrete, hyExists, hyGround⟩
        exact ih y hyGround hyConcrete hyExists
      · refine ⟨x, hxConcrete, hxExists, ?_⟩
        intro y hyConcrete hyExists hyGround
        exact hp ⟨y, hyConcrete, hyExists, hyGround⟩
  rcases hPop with ⟨x, hxConcrete, hxExists⟩
  rcases findRoot x hxConcrete hxExists with
    ⟨root, hrConcrete, hrExists, hrMinimal⟩
  have hrCont : ContingentAt m.ontic w root := by
    by_cases hCont : ContingentAt m.ontic w root
    · exact hCont
    · have hNec : NecessaryConcreteAt m w := by
        refine ⟨root, hrConcrete, hrExists, ?_⟩
        intro v hv
        by_cases hev : m.ontic.ExistsAt v root
        · exact hev
        · exact False.elim (hCont ⟨hrExists, ⟨v, hv, hev⟩⟩)
      exact False.elim (hNoNecessary hNec)
  exact ⟨root, hrConcrete, hrExists, hrCont, hrMinimal⟩

/-- Either a genuine actual contingent concrete root exists, or existential
grounding is not well-founded. This is a conditional partition, not a
refutation of either alternative; and 'not well-founded' does not uniquely
specify an infinite temporal history rather than a cycle. -/
theorem bruteRootOrNonWellFounded
    (m : Profile W B) (w : W)
    (hPop : InhabitedAt m w)
    (hNoNecessary : ¬ NecessaryConcreteAt m w) :
    (∃ root, m.concrete root ∧ m.ontic.ExistsAt w root ∧
       ContingentAt m.ontic w root ∧
       (∀ y, m.concrete y → m.ontic.ExistsAt w y →
         ¬ m.grounds w y root)) ∨
      ¬ WellFounded (m.grounds w) := by
  classical
  by_cases hWF : WellFounded (m.grounds w)
  · exact Or.inl (contingentBruteRootOfNoNecessary m w hPop hWF hNoNecessary)
  · exact Or.inr hWF

/-- Source-free, classical model-theoretic conditional: a populated
actual world which contains no rigidly necessary concrete individual must
have either a contingent concrete root without an incoming ground from an
actually existent concrete predecessor, or a non-well-founded grounding
relation. Neither horn is asserted metaphysically actual or impossible. -/
def BruteRootDisjunctionClaim : Prop :=
  ∀ (World Being : Type) (m : Profile World Being) (w : World),
    InhabitedAt m w → ¬ NecessaryConcreteAt m w →
      (∃ root, m.concrete root ∧ m.ontic.ExistsAt w root ∧
        ContingentAt m.ontic w root ∧
        (∀ y, m.concrete y → m.ontic.ExistsAt w y →
          ¬ m.grounds w y root)) ∨
        ¬ WellFounded (m.grounds w)

/-- Two complete worlds. In each, there is one root (second coordinate false)
and one child (second coordinate true). All four rigid candidates are concrete,
but each exists in exactly one of the two worlds. -/
def boundaryRival : Profile Bool (Bool × Bool) where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => x.1 = w
    Causes := fun w y x =>
      y.1 = w ∧ x.1 = w ∧ y.2 = false ∧ x.2 = true
  }
  concrete := fun _ => True
  grounds := fun w y x =>
    y.1 = w ∧ x.1 = w ∧ y.2 = false ∧ x.2 = true

/-- Each world is inhabited, so the example is not a vacuously empty model. -/
theorem boundaryRivalInhabited : ∀ w, InhabitedAt boundaryRival w := by
  intro w
  exact ⟨(w, false), True.intro, rfl⟩

/-- Every relation edge has distinct, existing concrete endpoints. -/
theorem boundaryRivalEdgesSound :
    ∀ w y x, boundaryRival.grounds w y x →
      boundaryRival.concrete y ∧ boundaryRival.concrete x ∧
      boundaryRival.ontic.ExistsAt w y ∧
      boundaryRival.ontic.ExistsAt w x ∧ y ≠ x := by
  intro w y x h
  refine ⟨True.intro, True.intro, h.1, h.2.1, ?_⟩
  intro heq
  have hf : y.2 = false := h.2.2.1
  have ht : x.2 = true := h.2.2.2
  rw [heq] at hf
  rw [hf] at ht
  cases ht

/-- Both worlds have well-founded immediate grounds (one edge per child). -/
theorem boundaryRivalWellFounded :
    ∀ w, WellFounded (boundaryRival.grounds w) := by
  intro w
  refine ⟨?_⟩
  intro ⟨a, rank⟩
  cases rank with
  | false =>
      apply Acc.intro
      intro y hy
      have h : false = true := hy.2.2.2
      cases h
  | true =>
      apply Acc.intro
      intro y hy
      apply Acc.intro
      intro z hz
      have hf : y.2 = false := hy.2.2.1
      have ht : y.2 = true := hz.2.2.2
      rw [hf] at ht
      cases ht

/-- Every noninitial child has a distinct existing concrete predecessor.
The universal law deliberately exempts the two initial roots. -/
theorem boundaryRivalNoninitialGrounded :
    ∀ w x, boundaryRival.concrete x →
      boundaryRival.ontic.ExistsAt w x → x.2 = true →
      ∃ y, boundaryRival.concrete y ∧
        boundaryRival.ontic.ExistsAt w y ∧
        boundaryRival.grounds w y x := by
  intro w x _ hx hChild
  exact ⟨(w, false), True.intro, rfl, ⟨rfl, hx, rfl, hChild⟩⟩

/-- Every existent is modally contingent: the other world lacks it. -/
theorem boundaryRivalAllContingent :
    ∀ w x, boundaryRival.ontic.ExistsAt w x →
      ContingentAt boundaryRival.ontic w x := by
  intro w x hx
  cases w with
  | false =>
      refine ⟨hx, ⟨true, True.intro, ?_⟩⟩
      intro ht
      have hf : x.1 = false := hx
      have ht' : x.1 = true := ht
      rw [hf] at ht'
      cases ht'
  | true =>
      refine ⟨hx, ⟨false, True.intro, ?_⟩⟩
      intro ht
      have hf : x.1 = true := hx
      have ht' : x.1 = false := ht
      rw [hf] at ht'
      cases ht'

/-- Despite universal accessibility, nonempty worlds, sound causal edges,
well-foundedness and locally caused noninitial beings, there is no de re
necessary concrete individual in this model. -/
theorem boundaryRivalNoNecessary :
    ¬ NecessaryConcreteAt boundaryRival false := by
  intro h
  rcases h with ⟨x, _, hex, hNec⟩
  rcases boundaryRivalAllContingent false x hex with ⟨_, v, hv, hAbsent⟩
  exact hAbsent (hNec v hv)

/-- The stronger all-contingent-grounded premise is precisely what fails:
the actual contingent root is not grounded by an existing predecessor. -/
theorem boundaryRivalHasBruteRoot :
    ¬ EveryContingentGroundedAt boundaryRival false := by
  intro hDep
  have hc : ContingentAt boundaryRival.ontic false (false, false) :=
    boundaryRivalAllContingent false (false, false) rfl
  rcases hDep (false, false) True.intro rfl hc with ⟨y, _, _, hGround⟩
  have h : false = true := hGround.2.2.2
  cases h

end TruthCore.Causality.BruteFoundationBoundary
