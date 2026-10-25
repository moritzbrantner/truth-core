import TruthCore.Modal.KResearch
namespace TruthCore.Results.Modal.K.Extensionality
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.KResearch

private theorem bool_eq (a b : Bool) (h : (a = true ↔ b = true)) : a = b := by
  cases a with
  | false =>
    cases b with
    | false => rfl
    | true => exact Bool.noConfusion (h.mpr rfl)
  | true =>
    cases b with
    | false => exact Bool.noConfusion (h.mp rfl)
    | true => rfl

theorem language_extensional (link : Bool) : PropositionalExtensionality (language link) := by
  intro w v h
  have same (φ : Formula Unit) : eval (fork link) w φ = eval (fork link) v φ := by
    apply bool_eq
    exact (eval_correct _ φ w).trans ((h _ ⟨φ, rfl⟩).trans (eval_correct _ φ v).symm)
  have ha := same (.atom ())
  have hd := same (.diamond (.imp .falsum .falsum))
  have hb := same (.box (.atom ()))
  cases link <;> cases w <;> cases v <;>
    first
    | rfl
    | exact Bool.noConfusion ha
    | exact Bool.noConfusion hd
    | exact Bool.noConfusion hb

theorem checks : ExtensionalCountermodels := by
  refine ⟨language_extensional, ?_⟩
  intro W w v h
  exact (h (fun x => x = w) trivial).mp rfl |>.symm
end TruthCore.Results.Modal.K.Extensionality
