module

public import TruthCore.Models.NecessaryWholeReplacement

@[expose] public section

namespace TruthCore.Results.Causality.NecessaryWholeReplacement

open TruthCore.Models.NecessarilyUnderived
open TruthCore.Models.NecessaryWholeReplacement
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.BruteFoundationBoundary

private theorem necessarySome (a : Role)
    (h : NecessaryAt profile.ontic false (some a)) :
    NecessaryAt switching false a := h

private theorem unionEmpty (a b : Candidate) :
    ¬ UnionNecessarySupport profile.ontic support false a b := by
  rintro ⟨ha, hb, w, hp, he⟩
  cases a with
  | none => exact he
  | some a =>
    cases b with
    | some b =>
      exact switchingUnionEmpty a b ⟨necessarySome a ha, necessarySome b hb, w, hp, he⟩
    | none =>
      rcases switchingNecessaryOnlyAB a (necessarySome a ha) with rfl | rfl <;>
        cases w <;> dsimp [support] at he <;> contradiction

private theorem worldWF (w : Bool) :
    WellFoundedPresentEsseSupport profile.ontic support w := by
  have hr : ∀ a b, PresentEsseSupport profile.ontic support w a b →
      rank w a < rank w b := by
    intro a b h
    have he := h.2
    cases w <;> cases a with
    | none => exact False.elim he
    | some a =>
      cases b with
      | none => cases a <;> dsimp [support, rank, switchingRank] at * <;> decide
      | some b =>
        cases a <;> cases b <;>
          dsimp [support, rank, switchingSupport, switchingRank] at * <;>
          first | contradiction | decide
  exact Subrelation.wf (fun {_ _} h => hr _ _ h)
    (InvImage.wf (rank w) Nat.lt_wfRel.wf)

theorem checks : Control := by
  refine ⟨(fun _ _ => trivial), trivial, ?_, ?_, worldWF, ?_, ?_, unionEmpty, ?_, ?_, ?_⟩
  · intro w
    cases w
    · exact ⟨some .c, (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide), (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide), true, (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide)⟩
    · exact ⟨some .d, (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide), (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide), false, (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide)⟩
  · intro w a b h
    cases w <;> cases a with
    | none => exact False.elim h
    | some a =>
      cases b with
      | none => cases a <;> dsimp [support, present, switchingExists] at * <;> simp_all
      | some b =>
        cases a <;> cases b <;>
          dsimp [support, present, switchingExists, switchingSupport] at * <;> simp_all
  · intro w x _ hx hc
    obtain ⟨_, v, _, hv⟩ := hc
    cases x with
    | none => exact False.elim (hv trivial)
    | some x =>
      cases x with
      | a => exact False.elim (hv (Or.inl rfl))
      | b => exact False.elim (hv (Or.inr (Or.inl rfl)))
      | c =>
        refine ⟨some .b, trivial, ?_, ?_⟩
        · exact Or.inr (Or.inl rfl)
        · cases w <;> dsimp [profile, present, switchingExists] at hx <;>
            dsimp [profile, support, switchingSupport] <;> simp_all
      | d =>
        refine ⟨some .a, trivial, Or.inl rfl, ?_⟩
        cases w <;> dsimp [profile, present, switchingExists] at hx <;>
          dsimp [profile, support, switchingSupport] <;> simp_all
  · intro v w a b h
    cases v <;> cases w <;> cases a with
    | none => exact False.elim h
    | some a =>
      cases b with
      | none => exact fun h => h
      | some b =>
        cases a <;> cases b <;> dsimp [support, switchingSupport] at * <;> simp_all
  · refine ⟨fun b => ⟨b, fun a h => False.elim ?_⟩⟩
    exact unionEmpty a.val b.val h
  · intro h
    have hn := h false ⟨some .c, trivial⟩ ⟨none, trivial⟩
      (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide) (fun _ _ => trivial) (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide)
    exact (by dsimp [present, switchingExists]; decide : ¬ present true (some .c)) (hn true trivial)
  · rintro ⟨x, _, hx, hn, hu⟩
    cases x with
    | none => exact hu false (some .c) trivial (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide) (by dsimp [concreteOntic, concreteSupport, profile, present, support, switchingExists]; decide)
    | some a =>
      apply switchingNoUnderived
      refine ⟨a, hx, necessarySome a hn, ?_⟩
      intro w b hb he
      exact hu w (some b) trivial hb he

end TruthCore.Results.Causality.NecessaryWholeReplacement
