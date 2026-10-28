import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.WithBot
import TruthCore.Causality.WorldSourceRegress
namespace TruthCore.Results.Causality.WorldSourceRegress
open TruthCore.Causality
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference

theorem actualSource_iff {World Being : Type} (m : Ontic World Being) (w : World)
    (x : Actual m w) : (actualGraph m w).Source x ↔
    ¬ ∃ y, m.ExistsAt w y ∧ m.Causes w y x.val := by
  constructor
  · intro hs ⟨y, hy, he⟩
    exact hs ⟨⟨y, hy⟩, he⟩
  · intro hs ⟨y, he⟩
    exact hs ⟨y.val, y.property, he⟩

theorem sourcePath_of_acc {Node : Type} (G : Graph Node) (x : Node)
    (hAcc : Acc G.edge x) : SourcePath G x := by
  have hg : FinitelyGroundedPower G.edge G.Source x := by
    classical
    induction hAcc with
    | intro x _ ih =>
      by_cases hs : ∃ y, G.edge y x
      · obtain ⟨y, hy⟩ := hs
        exact .borrowed hy (ih y hy)
      · exact .intrinsic x hs
  exact TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource
    Node G.edge G.Source x hg

theorem chain_injective {Node : Type} (G : Graph Node) (hNoCycles : G.NoCycles)
    (f : Nat → Node) (hStep : ∀ n, G.edge (f (n + 1)) (f n)) :
    Function.Injective f := by
  let : IsTrans Node (fun a b => Relation.TransGen G.edge b a) :=
    ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  have hPath {i j : Nat} (hij : i < j) : Relation.TransGen G.edge (f j) (f i) :=
    Nat.rel_of_forall_rel_succ_of_lt (fun a b => Relation.TransGen G.edge b a)
      (f := f) (fun n => Relation.TransGen.single (hStep n)) hij
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (hNoCycles (f j) (by simpa only [heq] using hPath hij))
  · exact hij
  · exact False.elim (hNoCycles (f j) (by simpa only [heq] using hPath hji))

theorem source_or_regress {Node : Type} (G : Graph Node) (hNoCycles : G.NoCycles)
    (x : Node) : SourcePath G x ∨ AnchoredRegress G x := by
  classical
  by_cases hAcc : Acc G.edge x
  · exact Or.inl (sourcePath_of_acc G x hAcc)
  · obtain ⟨f, h0, hStep⟩ := not_acc_iff_exists_descending_chain.mp hAcc
    exact Or.inr ⟨f, h0, chain_injective G hNoCycles f hStep, hStep⟩

theorem worldProjection {World Being : Type} (m : Ontic World Being)
    (hNoCycles : ActualAcyclic m) :
    {w | ∃ x, m.ExistsAt w x} = StarterWorlds m ∪ RegressWorlds m := by
  apply Set.ext
  intro w
  change (∃ x, m.ExistsAt w x) ↔
    (∃ s : Actual m w, (actualGraph m w).Source s) ∨
      ∃ x : Actual m w, AnchoredRegress (actualGraph m w) x
  constructor
  · rintro ⟨x, hx⟩
    rcases source_or_regress (actualGraph m w) (hNoCycles w) ⟨x, hx⟩ with hs | hr
    · obtain ⟨s, _, hs⟩ := hs
      exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨⟨x, hx⟩, hr⟩
  · rintro (⟨s, _⟩ | ⟨x, _⟩)
    · exact ⟨s.val, s.property⟩
    · exact ⟨x.val, x.property⟩

theorem finite_source {Node : Type} (G : Graph Node) [Finite Node]
    (hNoCycles : G.NoCycles) (x : Node) : ∃ s, G.Source s := by
  rcases source_or_regress G hNoCycles x with hs | hr
  · obtain ⟨s, _, hs⟩ := hs
    exact ⟨s, hs⟩
  · obtain ⟨f, _, hInj, _⟩ := hr
    exact False.elim (not_injective_infinite_finite f hInj)

theorem checks {World Being : Type} (m : Ontic World Being)
    (hNoCycles : ActualAcyclic m) : WorldClassification m := by
  refine ⟨fun w x => source_or_regress (actualGraph m w) (hNoCycles w) x,
    worldProjection m hNoCycles, ?_⟩
  intro w hFinite ⟨x, hx⟩
  let : Finite (Actual m w) := hFinite
  exact finite_source (actualGraph m w) (hNoCycles w) ⟨x, hx⟩

theorem overlapControl : OverlapControl := by
  let link := TruthCore.Results.Causality.GroundingAllowsRegress.link
  -- WithTop Nat is a standard order witness for acyclicity, not time or WF.
  let rank : Option Nat → WithTop Nat := fun x => x
  have lower : ∀ y x, link y x → rank x < rank y := by
    intro y x he
    cases y with
    | none =>
      cases x with
      | none => exact False.elim he
      | some n =>
        change (n : WithTop Nat) < ⊤
        exact WithTop.coe_lt_top n
    | some m =>
      cases x with
      | none => exact False.elim he
      | some n =>
        change m = n + 1 at he
        subst m
        exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)
  have lowerPath : ∀ {a b}, Relation.TransGen link a b → rank b < rank a := by
    intro a b hp
    induction hp with
    | single he => exact lower _ _ he
    | tail _ he ih => exact lt_trans (lower _ _ he) ih
  have hNoCycles : ActualAcyclic overlap := by
    intro w x hp
    have hLift : Relation.TransGen link x.val x.val :=
      Relation.TransGen.lift Subtype.val (fun _ _ he => he) x x hp
    exact (lt_irrefl (rank x.val)) (lowerPath hLift)
  let G := actualGraph overlap ()
  let source : Actual overlap () := ⟨none, True.intro⟩
  have noIncoming (y : Option Nat) : ¬ link y none := by
    cases y <;> exact id
  have hSource : G.Source source := by
    rintro ⟨y, he⟩
    change link y.val none at he
    exact noIncoming y.val he
  have hPath : SourcePath G overlapNode :=
    ⟨source, .link (y := source) True.intro (.same source), hSource⟩
  let f : Nat → Actual overlap () := fun n => ⟨some n, True.intro⟩
  have hInj : Function.Injective f := by
    intro i j he
    exact Option.some.inj (congrArg Subtype.val he)
  have hStep : ∀ n, G.edge (f (n + 1)) (f n) := fun _ => rfl
  have hRegress : AnchoredRegress G overlapNode := ⟨f, rfl, hInj, hStep⟩
  have hNotAcc : ¬ Acc G.edge overlapNode :=
    not_acc_iff_exists_descending_chain.mpr ⟨f, rfl, hStep⟩
  exact ⟨hNoCycles, hPath, hRegress, hNotAcc, ⟨source, hSource⟩,
    ⟨overlapNode, hRegress⟩⟩
end TruthCore.Results.Causality.WorldSourceRegress
