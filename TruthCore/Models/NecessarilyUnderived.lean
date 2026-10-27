import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Models.FiniteSupport

/-!
# Independent finite controls for necessary underived existence

These are formal structures, not claims that their support relations describe
metaphysical possibilities. In particular, an ungrounded individual in the
signature is not thereby God or a self-explaining existence fact.
-/

namespace TruthCore.Models.NecessarilyUnderived

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived

/-! ## Missing premise: necessary population -/

def emptySupport (_ : Unit) (_ _ : Unit) : Prop := False

def empty : Ontic Unit Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => False
  Causes := emptySupport

theorem emptyWellFounded :
    WellFoundedPresentEsseSupport empty emptySupport () := by
  refine ⟨?_⟩
  intro target
  apply Acc.intro
  intro source h
  exact False.elim h.1

theorem emptyLifting : NecessaryPredecessorLifting empty emptySupport () := by
  intro _ _ _ _ hExists _
  exact False.elim hExists

theorem emptyNoNecessary : ¬ NecessaryBeing empty () := by
  rintro ⟨_, hExists, _⟩
  exact hExists

theorem emptyNoUnderived : ¬ NecessarilyUnderived empty emptySupport () := by
  rintro ⟨_, hExists, _, _⟩
  exact hExists

/-! ## Missing premise: well-foundedness -/

/-- Both present necessary individuals support the other's existence. The
source graph has a directed 2-cycle, so no underived bearer exists. -/
def loopSupport (_ : Unit) (source target : Bool) : Prop := source ≠ target

def loop : Ontic Unit Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := loopSupport

theorem loopNecessary : NecessaryBeing loop () := by
  refine ⟨false, trivial, ?_⟩
  intro _ _
  trivial

theorem loopLifting : NecessaryPredecessorLifting loop loopSupport () := by
  intro _ _ _ _ _ hEdge
  exact ⟨(by intro _ _; trivial), trivial, hEdge⟩

theorem loopNoUnderived : ¬ NecessarilyUnderived loop loopSupport () := by
  rintro ⟨target, _, _, hNoSource⟩
  cases target with
  | false =>
      exact (hNoSource () true (by trivial)) (by unfold loopSupport; decide)
  | true =>
      exact (hNoSource () false (by trivial)) (by unfold loopSupport; decide)

theorem loopNotWellFounded :
    ¬ WellFoundedPresentEsseSupport loop loopSupport () := by
  intro hWF
  exact (not_not_underived_of_lifting loop loopSupport ()
    loopNecessary hWF loopLifting) loopNoUnderived

/-! ## Missing premise: cross-world predecessor lifting -/

/-- Both Bool individuals exist necessarily. The sole incoming edge reverses
direction between universally accessible worlds, so each local graph is a
finite well-founded DAG, but their union contains a 2-cycle. -/
def rotatingSupport (w source target : Bool) : Prop :=
  (w = false ∧ source = false ∧ target = true) ∨
  (w = true ∧ source = true ∧ target = false)

def rotating : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := rotatingSupport

def rotatingRank (w individual : Bool) : Nat :=
  if w = individual then 0 else 1

theorem rotatingWorldWellFounded (w : Bool) :
    WellFounded (PresentEsseSupport rotating rotatingSupport w) := by
  have hSub : ∀ source target,
      PresentEsseSupport rotating rotatingSupport w source target →
      rotatingRank w source < rotatingRank w target := by
    intro source target
    cases w <;> cases source <;> cases target <;>
      dsimp [PresentEsseSupport, rotating, rotatingSupport, rotatingRank] <;> decide
  exact Subrelation.wf (fun {_ _} h => hSub _ _ h)
    (InvImage.wf (rotatingRank w) Nat.lt_wfRel.wf)

theorem rotatingActualWellFounded :
    WellFoundedPresentEsseSupport rotating rotatingSupport false :=
  rotatingWorldWellFounded false

theorem rotatingNecessary : NecessaryBeing rotating false := by
  refine ⟨false, trivial, ?_⟩
  intro _ _
  trivial

theorem rotatingReflexive : ActualReflexive rotating false := by trivial

theorem rotatingNoContingentGround :
    NoContingentGroundOfNecessary rotating rotatingSupport false := by
  intro _ _ _ _ _ _ _ _
  trivial

theorem rotatingNoUnderived :
    ¬ NecessarilyUnderived rotating rotatingSupport false := by
  rintro ⟨individual, _, _, hNoSource⟩
  cases individual with
  | false =>
      exact (hNoSource true true (by trivial)) (by unfold rotatingSupport; decide)
  | true =>
      exact (hNoSource false false (by trivial)) (by unfold rotatingSupport; decide)

theorem rotatingNoLifting :
    ¬ NecessaryPredecessorLifting rotating rotatingSupport false := by
  intro hLift
  exact (not_not_underived_of_lifting rotating rotatingSupport false
    rotatingNecessary rotatingActualWellFounded hLift) rotatingNoUnderived

theorem rotatingUnionNotWellFounded :
    ¬ WellFoundedUnionNecessarySupport rotating rotatingSupport false := by
  intro hWF
  exact (not_not_underived_of_union_wellFounded rotating rotatingSupport false
    rotatingNecessary rotatingReflexive rotatingNoContingentGround hWF)
    rotatingNoUnderived

/-! ## Missing premise: contingent supporters of necessary beings -/

/-- Necessary `a,b` are present in both worlds. Contingent `c` appears only
in the first world and `d` only in the second. -/
inductive Role where
  | a | b | c | d
  deriving DecidableEq

theorem enumerateRole :
    ∀ individual : Role, individual = .a ∨ individual = .b ∨
      individual = .c ∨ individual = .d := by
  intro individual
  cases individual <;> decide

def switchingExists (w : Bool) (individual : Role) : Prop :=
  individual = .a ∨ individual = .b ∨
    (w = false ∧ individual = .c) ∨ (w = true ∧ individual = .d)

/-- `b → c → a` in the first world and `a → d → b` in the second. Direct
support between two necessary individuals never occurs in either world. -/
def switchingSupport (w : Bool) (source target : Role) : Prop :=
  (w = false ∧ ((source = .b ∧ target = .c) ∨
                 (source = .c ∧ target = .a))) ∨
  (w = true ∧ ((source = .a ∧ target = .d) ∨
                (source = .d ∧ target = .b)))

def switching : Ontic Bool Role where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := switchingExists
  Causes := switchingSupport

def switchingRank (w : Bool) (individual : Role) : Nat :=
  if w = false then
    if individual = .b then 0 else if individual = .c then 1
      else if individual = .a then 2 else 0
  else
    if individual = .a then 0 else if individual = .d then 1
      else if individual = .b then 2 else 0

theorem switchingWorldWellFounded (w : Bool) :
    WellFounded (PresentEsseSupport switching switchingSupport w) := by
  have hSub : ∀ source target,
      PresentEsseSupport switching switchingSupport w source target →
      switchingRank w source < switchingRank w target := by
    intro source target
    cases w <;> cases source <;> cases target <;>
      dsimp [PresentEsseSupport, switching, switchingExists, switchingSupport,
        switchingRank] <;> decide
  exact Subrelation.wf (fun {_ _} h => hSub _ _ h)
    (InvImage.wf (switchingRank w) Nat.lt_wfRel.wf)

theorem switchingActualWellFounded :
    WellFoundedPresentEsseSupport switching switchingSupport false :=
  switchingWorldWellFounded false

theorem switchingNecessary : NecessaryBeing switching false := by
  refine ⟨.a, (by dsimp [switching, switchingExists]; decide), ?_⟩
  intro w _
  cases w <;> dsimp [switching, switchingExists] <;> decide

theorem switchingReflexive : ActualReflexive switching false := by trivial

theorem switchingNecessaryOnlyAB (individual : Role) :
    NecessaryAt switching false individual → individual = .a ∨ individual = .b := by
  intro hNecessary
  cases individual with
  | a => exact Or.inl rfl
  | b => exact Or.inr rfl
  | c =>
      have hPresent := hNecessary true (by trivial)
      have hAbsent : ¬ switching.ExistsAt true .c := by
        dsimp [switching, switchingExists]
        decide
      exact False.elim (hAbsent hPresent)
  | d =>
      have hPresent := hNecessary false (by trivial)
      have hAbsent : ¬ switching.ExistsAt false .d := by
        dsimp [switching, switchingExists]
        decide
      exact False.elim (hAbsent hPresent)

/-- The union of *direct* support edges between necessary individuals is
empty. This demonstrates why union-WF alone cannot rule out a contingent
intermediary in a support chain. -/
theorem switchingUnionEmpty (source target : Role) :
    ¬ UnionNecessarySupport switching switchingSupport false source target := by
  rintro ⟨hSourceNecessary, hTargetNecessary, w, _, hSupport⟩
  rcases switchingNecessaryOnlyAB source hSourceNecessary with rfl | rfl <;>
    rcases switchingNecessaryOnlyAB target hTargetNecessary with rfl | rfl <;>
    cases w <;>
    exact (by dsimp [switchingSupport]; decide : ¬ switchingSupport _ _ _) hSupport

theorem switchingUnionWellFounded :
    WellFoundedUnionNecessarySupport switching switchingSupport false := by
  refine ⟨?_⟩
  intro target
  apply Acc.intro
  intro source h
  exact False.elim (switchingUnionEmpty source target h)

theorem switchingHasContingentGround :
    ¬ NoContingentGroundOfNecessary switching switchingSupport false := by
  intro h
  have hNecessaryA : NecessaryAt switching false .a := by
    intro w _
    cases w <;> dsimp [switching, switchingExists] <;> decide
  have hNecessaryC := h false .c .a
    (by dsimp [switching, switchingExists]; decide) hNecessaryA
    (by unfold switchingSupport; decide)
  have hc := hNecessaryC true (by trivial)
  have hAbsent : ¬ switching.ExistsAt true .c := by
    dsimp [switching, switchingExists]
    decide
  exact hAbsent hc

theorem switchingNoUnderived :
    ¬ NecessarilyUnderived switching switchingSupport false := by
  rintro ⟨individual, _, hNecessary, hNoSource⟩
  cases individual with
  | a =>
      exact (hNoSource false .c (by dsimp [switching, switchingExists]; decide))
        (by unfold switchingSupport; decide)
  | b =>
      exact (hNoSource true .d (by dsimp [switching, switchingExists]; decide))
        (by unfold switchingSupport; decide)
  | c =>
      have hc := hNecessary true (by trivial)
      have hAbsent : ¬ switching.ExistsAt true .c := by
        dsimp [switching, switchingExists]
        decide
      exact hAbsent hc
  | d =>
      have hd := hNecessary false (by trivial)
      have hAbsent : ¬ switching.ExistsAt false .d := by
        dsimp [switching, switchingExists]
        decide
      exact hAbsent hd

theorem switchingNoLifting :
    ¬ NecessaryPredecessorLifting switching switchingSupport false := by
  intro hLift
  exact (not_not_underived_of_lifting switching switchingSupport false
    switchingNecessary switchingActualWellFounded hLift) switchingNoUnderived

/-- Every *present contingent* individual has an incoming existing direct
supporter. This does not prohibit its grounding a necessary bearer. -/
theorem switchingContingentDependence :
    ∀ w individual, ContingentAt switching w individual →
      ∃ source, switching.ExistsAt w source ∧
        switchingSupport w source individual := by
  intro w individual hCont
  cases w with
  | false =>
      cases individual with
      | a =>
          obtain ⟨_, v, _, hv⟩ := hCont
          cases v <;> simp [switching, switchingExists] at hv
      | b =>
          obtain ⟨_, v, _, hv⟩ := hCont
          cases v <;> simp [switching, switchingExists] at hv
      | c =>
          exact ⟨.b, (by simp [switching, switchingExists]),
            (by simp [switchingSupport])⟩
      | d =>
          have he := hCont.1
          simp [switching, switchingExists] at he
  | true =>
      cases individual with
      | a =>
          obtain ⟨_, v, _, hv⟩ := hCont
          cases v <;> simp [switching, switchingExists] at hv
      | b =>
          obtain ⟨_, v, _, hv⟩ := hCont
          cases v <;> simp [switching, switchingExists] at hv
      | c =>
          have he := hCont.1
          simp [switching, switchingExists] at he
      | d =>
          exact ⟨.a, (by simp [switching, switchingExists]),
            (by simp [switchingSupport])⟩

/-! ## World-varying edges can still have a well-founded union -/

/-- Nothing directly supports anything in the actual world. In the other
world the necessary individual `false` supports `true`. The union remains a
finite well-founded order even though there is a *novel* possible-world edge.
This is a strict countermodel to the converse of `union_wellFounded_of_actual_wellFounded`. -/
def varyingSupport (w source target : Bool) : Prop :=
  w = true ∧ source = false ∧ target = true

def varying : Ontic Bool Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := varyingSupport

theorem varyingNecessary : NecessaryBeing varying false := by
  refine ⟨false, trivial, ?_⟩
  intro _ _
  trivial

theorem varyingReflexive : ActualReflexive varying false := by trivial

theorem varyingNoContingentGround :
    NoContingentGroundOfNecessary varying varyingSupport false := by
  intro _ _ _ _ _ _ _ _
  trivial

theorem varyingActualWellFounded :
    WellFoundedPresentEsseSupport varying varyingSupport false := by
  refine ⟨?_⟩
  intro target
  apply Acc.intro
  intro source h
  cases h.2.1

def varyingRank (individual : Bool) : Nat :=
  if individual = false then 0 else 1

theorem varyingUnionWellFounded :
    WellFoundedUnionNecessarySupport varying varyingSupport false := by
  have hSub : ∀ source target,
      UnionNecessarySupport varying varyingSupport false source target →
      varyingRank source < varyingRank target := by
    intro source target ⟨_, _, w, _, hEdge⟩
    rcases hEdge with ⟨rfl, rfl, rfl⟩
    decide
  exact Subrelation.wf (fun {_ _} h => hSub _ _ h)
    (InvImage.wf varyingRank Nat.lt_wfRel.wf)

theorem varyingNoNovelSupport :
    ¬ NoNovelNecessarySupport varying varyingSupport false := by
  intro h
  have hNecFalse : NecessaryAt varying false false := by
    intro _ _
    trivial
  have hNecTrue : NecessaryAt varying false true := by
    intro _ _
    trivial
  have hEdge : varyingSupport true false true := ⟨rfl, rfl, rfl⟩
  have hActual := h true false true hNecFalse hNecTrue (by trivial) hEdge
  cases hActual.1

theorem varyingUnderived : NecessarilyUnderived varying varyingSupport false := by
  refine ⟨false, trivial, (by intro _ _; trivial), ?_⟩
  intro w source _ hEdge
  cases hEdge.2.2

theorem varyingNoLifting :
    ¬ NecessaryPredecessorLifting varying varyingSupport false := by
  intro h
  have hNecessaryTrue : NecessaryAt varying false true := by
    intro _ _
    trivial
  obtain ⟨_, hActual⟩ := h true false true hNecessaryTrue
    (by trivial) ⟨rfl, rfl, rfl⟩
  cases hActual.2.1

end TruthCore.Models.NecessarilyUnderived
