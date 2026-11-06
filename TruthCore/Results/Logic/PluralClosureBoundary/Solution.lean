module

public import TruthCore.Logic.PluralClosureBoundary

@[expose] public section
namespace TruthCore.Results.Logic.PluralClosureBoundary
open TruthCore.Logic.PluralClosureBoundary

private def kCounter : Valuation := fun a => if a then (false, false) else (true, false)
private def lCounter : Valuation := fun a => if a then (true, true) else (false, true)
private def positive : Valuation := fun a => if a then (false, true) else (true, false)
private def negative : Valuation := fun _ => (false, true)

private theorem kAdmitted : Admissible .k3 kCounter := by
  intro a
  cases a <;> decide
private theorem lAdmitted : Admissible .lp lCounter := by
  intro a
  cases a <;> decide

private theorem andParts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b
  all_goals first | exact ⟨rfl, rfl⟩ | cases h

private theorem andIntro {a b : Bool} (h : a = true ∧ b = true) : (a && b) = true := by
  cases h.1
  cases h.2
  rfl

private theorem orParts {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b
  all_goals first | exact Or.inl rfl | exact Or.inr rfl | cases h

private theorem orIntro {a b : Bool} (h : a = true ∨ b = true) : (a || b) = true := by
  rcases h with ha | hb
  · cases ha
    rfl
  · cases hb
    cases a <;> rfl

private theorem kStep : Consequence .k3 [premise] p := by
  intro v hv hΓ
  have hg := hΓ premise (List.Mem.head [])
  change (v false).1 || ((v true).1 && (v true).2) = true at hg
  rcases orParts hg with hp | hBoth
  · exact hp
  · exact False.elim (hv true (andParts hBoth))

private theorem lLem : Consequence .lp [] lemQ := by
  intro v hv _
  exact orIntro (hv true)

private theorem conjunction (L : Profile) (a b : Formula) :
    Consequence L [a, b] (.conj a b) := by
  intro v _ hΓ
  exact andIntro
    ⟨hΓ a (List.Mem.head [b]), hΓ b (List.Mem.tail a (List.Mem.head []))⟩

private theorem singletonMembers (v : Valuation) (hg : Designated v premise) :
    ∀ a ∈ [premise], Designated v a := by
  intro a ha
  cases ha with
  | head => exact hg
  | tail _ h => cases h

private theorem notK : ¬ Consequence .k3 [premise] conclusion := by
  intro h
  have hd := h kCounter kAdmitted (singletonMembers kCounter rfl)
  change false = true at hd
  cases hd

private theorem notL : ¬ Consequence .lp [premise] conclusion := by
  intro h
  have hd := h lCounter lAdmitted (singletonMembers lCounter rfl)
  change false = true at hd
  cases hd

private theorem semantic : SemanticBoundary := by
  refine ⟨kStep, ?_, lLem, ?_, conjunction, notK, notL⟩
  · intro h
    have hd := h lCounter lAdmitted (singletonMembers lCounter rfl)
    change false = true at hd
    cases hd
  · intro h
    have hd := h kCounter kAdmitted (by intro a ha; cases ha)
    change false = true at hd
    cases hd

theorem joint : JointClosureLaw := by
  intro B hg hk hl
  have hp := hk [premise] p
    (by intro a ha; cases ha with
        | head => exact hg
        | tail _ h => cases h) kStep
  have hem := hl [] lemQ (by intro a ha; cases ha) lLem
  exact hk [p, lemQ] conclusion
    (by intro a ha; cases ha with
        | head => exact hp
        | tail _ h => cases h with
          | head => exact hem
          | tail _ h => cases h)
    (conjunction .k3 p lemQ)

private theorem theoryInitial (L : Profile) : Theory L premise premise := by
  intro v _ hΓ
  exact hΓ premise (List.Mem.head [])

private theorem theoryClosed (L : Profile) : Closed L (Theory L premise) := by
  intro Γ a hMembers hStep v hv hInitial
  exact hStep v hv (fun b hb => hMembers b hb v hv hInitial)

private theorem designatedClosed (L : Profile) (v : Valuation) (hv : Admissible L v) :
    Closed L (DesignatedPool v) := by
  intro Γ a members step
  exact step v hv members

private theorem positiveK : Admissible .k3 positive := by
  intro a
  cases a <;> decide
private theorem positiveL : Admissible .lp positive := by
  intro a
  cases a <;> decide
private theorem negativeK : Admissible .k3 negative := by
  intro a
  cases a <;> decide
private theorem negativeL : Admissible .lp negative := by
  intro a
  cases a <;> decide

private theorem deletions : DeletionControls := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Theory .k3 premise, theoryInitial .k3, theoryClosed .k3, ?_, notK⟩
    intro hl
    exact notK (joint _ (theoryInitial .k3) (theoryClosed .k3) hl)
  · refine ⟨Theory .lp premise, theoryInitial .lp, theoryClosed .lp, ?_, notL⟩
    intro hk
    exact notL (joint _ (theoryInitial .lp) hk (theoryClosed .lp))
  · exact ⟨DesignatedPool negative,
      designatedClosed .k3 negative negativeK, designatedClosed .lp negative negativeL,
      by change ¬ (false = true); decide, by change ¬ (false = true); decide⟩

private theorem survivors : SurvivorControls := by
  constructor
  · exact ⟨DesignatedPool positive, by rfl,
      designatedClosed .k3 positive positiveK, designatedClosed .lp positive positiveL,
      by rfl, by change ¬ (false = true); decide⟩
  · exact ⟨Theory .k3 premise, Theory .lp premise, theoryInitial .k3, theoryInitial .lp,
      theoryClosed .k3, theoryClosed .lp, notK, notL⟩

theorem checks : Certificate := ⟨semantic, joint, deletions, survivors⟩

end TruthCore.Results.Logic.PluralClosureBoundary
