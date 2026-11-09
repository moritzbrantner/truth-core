module
public import TruthCore.Hiddenness.ActualRoot
@[expose] public section
namespace TruthCore.Hiddenness.WitnessLocalHiddenness
open TruthCore.Hiddenness TruthCore.Hiddenness.ActualRoot
/-- Same empirical conditions as NonresistantNonbelief, with the witness exposed. -/
def Gap (s : Sig) (p : s.Person) (t : s.Time) : Prop :=
  s.Capable s.actual p t ∧ ¬ s.Resists s.actual p t ∧ ¬ s.Believes s.actual p t
/-- Only nonbelief witnesses need immediate access. No claim about believers. -/
def WitnessOpen (s : Sig) : Prop :=
  ∀ p t, Gap s p t → s.PerfectLove s.actual → s.Available s.actual p t
/-- Only capable causal nonresisters are covered. -/
def WitnessAccess (s : Sig) : Prop :=
  ∀ p t, Gap s p t → ¬ s.Available s.actual p t
/-- Stronger scope weakening: one aligned witness suffices; the existential
is outside God/love implications, with no choice depending on supposed God.
This bundles the unchanged empirical conditions with two local norms. -/
def SelectedBundle (s : Sig) : Prop :=
  ∃ p t, Gap s p t ∧
    (s.PerfectLove s.actual → s.Available s.actual p t) ∧
    ¬ s.Available s.actual p t
/-- Actual God-to-love has no person/time scope to restrict. Guarding it by
NonresistantNonbelief is equivalent once that empirical premise is retained. -/
def GuardedLove (s : Sig) : Prop := NonresistantNonbelief s → ActualGodLoves s
/-- Two-time strictness model: the gap is early, the norm fails only late. -/
def scopeModel (access : Bool) : Sig :=
  { finiteModel false true false false with
    Believes := fun _ _ t => if access then False else t = true
    Capable := fun _ _ t => if access then t = false else True
    Available := fun _ _ t => if access then t = true else t = false }
def Controls : Prop :=
  (∃ s, WitnessOpen s ∧ NonresistantNonbelief s ∧ ¬ ActualAlwaysOpen s) ∧
  (∃ s, WitnessAccess s ∧ NonresistantNonbelief s ∧ ¬ ActualAccessNeedsBelief s) ∧
  (∃ s, ActualGodLoves s ∧ SelectedBundle s ∧ NoGod s) ∧
  (∃ s, WitnessOpen s ∧ WitnessAccess s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ WitnessAccess s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ WitnessOpen s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ WitnessOpen s ∧ WitnessAccess s ∧ GodExists s) ∧
  (∃ s, GodLoves s ∧ QualifiedOpen s ∧ AccessNeedsBelief s ∧
    ReasonForEachGap s ∧ GodExists s ∧ NonresistantNonbelief s ∧ ¬ WitnessOpen s ∧
    ∃ p t, Gap s p t ∧ s.GoodReason s.actual p t ∧ ¬ s.Accepts s.actual p t)
end TruthCore.Hiddenness.WitnessLocalHiddenness
