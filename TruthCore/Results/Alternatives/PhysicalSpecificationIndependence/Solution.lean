module
public import TruthCore.Alternatives.PhysicalSpecificationIndependence

@[expose] public section
namespace TruthCore.Results.Alternatives.PhysicalSpecificationIndependence
open FirstOrder TruthCore.Alternatives.PhysicalSpecification TruthCore.Alternatives.PhysicalGround

private theorem natReach (x : Nat) :
    Path (fun u w : Nat => w = u + 2) 0 x ↔ Even x := by
  constructor
  · intro h
    have key : ∀ a y : Nat, Path (fun u w : Nat => w = u + 2) a y → Even a → Even y := by
      intro a y h
      induction h with
      | refl => exact id
      | step e _ ih =>
        rintro ⟨r, hr⟩
        refine ih ⟨r + 1, ?_⟩
        rw [e, hr]
        exact (Nat.add_add_add_comm r 1 r 1).symm
    exact key 0 x h ⟨0, rfl⟩
  · rintro ⟨k, rfl⟩
    rw [path_iff_reflTransGen]
    induction k with
    | zero => exact .refl
    | succ n ih => exact ih.tail (Nat.add_add_add_comm n 1 n 1)

private theorem boolReach (x : Bool) :
    Path (fun _ _ : Bool => False) false x ↔ x = false := by
  constructor
  · intro h
    cases h with
    | refl => rfl
    | step e _ => exact e.elim
  · rintro rfl
    exact .refl _

private theorem anchorReach_iff (b : Bool) (x : evenDomain b) :
    anchorReach.realize (evenModel b).model
      (Sum.elim (fun _ => x) (fun a => (evenModel b).parameter a.val)) ↔ evenTarget b x := by
  cases b with
  | false => exact natReach x
  | true => exact boolReach x

theorem reachNontrivial : reachNontrivialControl := by
  refine ⟨⟨⟨false, trivial⟩, anchorReach, fun b _ x => anchorReach_iff b x⟩,
    anchorReach_iff, ?_, ?_, ?_⟩
  · change ¬ Even 1
    rintro ⟨k, hk⟩
    cases k with
    | zero => exact Nat.one_ne_zero hk
    | succ k =>
      have h0 : 0 = k + 1 + k := Nat.succ.inj hk
      rw [Nat.add_right_comm] at h0
      exact Nat.succ_ne_zero _ h0.symm
  · change ¬ (true = false)
    exact Bool.noConfusion
  · change Even 2
    exact ⟨1, rfl⟩

theorem routeIndependence : routeIndependenceControl := by
  refine ⟨⟨evenModel false, intellectualRoute⟩, ⟨evenModel false, componentRoute⟩,
    ⟨rfl, fun _ _ => Iff.rfl⟩, fun x => anchorReach_iff false x, ?_, ?_, trivial, rfl,
    fun h => h, fun h => h⟩
  · intro x hm _
    change ¬ x ≠ 0 at hm
    change x = 0
    exact not_not.mp hm
  · intro x hm hc
    change ¬ x ≠ 0 at hm
    exact (hc 2 ⟨not_not.mp hm, rfl⟩).elim

end TruthCore.Results.Alternatives.PhysicalSpecificationIndependence
