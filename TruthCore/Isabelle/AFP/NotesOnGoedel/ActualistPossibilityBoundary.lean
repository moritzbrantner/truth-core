import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1

/-! Source-free consequences of the already encoded 1970 definitions. This
boundary concerns the actualist possibility antecedent, not ordinary theism,
Scott's different essence definition, or inconsistency of the partial axioms. -/
namespace TruthCore.Isabelle.AFP.NotesOnGoedel.ActualistPossibilityBoundary
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity GodLike Dia)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

/-- No world possibly contains an actually existing God-like individual in the
1970 interpretation. This does not exclude actual God-likeness at an isolated
world, since possibility requires an accessibility edge. -/
def NoPossibleActualistGodLike {World Ind : Type} (F : Frame World)
    (ex : ExistsAt World Ind) (P : Positivity World Ind) : Prop :=
  ∀ w, ¬ Dia F (fun v => ∃ x, ex x v ∧ GodLike P x v) w

end TruthCore.Isabelle.AFP.NotesOnGoedel.ActualistPossibilityBoundary
