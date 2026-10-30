import TruthCore.Logic.TruthNontriviality
import TruthCore.Results.Logic.TruthNontriviality.Core.Solution
import TruthCore.Results.Logic.TruthPilot.LocalVariation.Solution
namespace TruthCore.Results.Logic.TruthNontriviality.Controls
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
open TruthCore.Logic.TruthPilot
open TruthCore.Logic.TruthNontriviality
open TruthCore.Results.Logic.TruthNontriviality.Core

/-- Contents are Lean propositions with a tag, truth is the proposition. The
holding domain is the true contents, the failing domain the false ones. -/
theorem localCollapseModel : LocalCollapseModel := by
  have hExpr : Expressive (fun c : Prop × Bool => c.1) :=
    fun P => ⟨(P, true), Iff.rfl⟩
  refine ⟨Prop × Bool, fun c => c.1, ⟨fun c => c.1⟩, ⟨fun c => ¬ c.1⟩, hExpr,
    not_collapse_of_expressive hExpr, ?_, fun _ h => h, ?_, fun _ h => h⟩
  · refine ⟨(True, true), (True, false), ?_, trivial, trivial⟩
    intro h
    cases congrArg Prod.snd h
  · refine ⟨(False, true), (False, false), ?_, fun h => h, fun h => h⟩
    intro h
    cases congrArg Prod.snd h

/-- The first model reads every sentence from the first agent's logical-sentence
endorsement; the second reads each sentence from that agent's own endorsement. -/
theorem profileVariationModels : ProfileVariationModels := by
  refine ⟨?_, ?_, TruthCore.Results.Logic.TruthPilot.LocalVariation.localVariation⟩
  · refine ⟨fun E _ => E Agent.first Sentence.logical, ?_, fun _ _ _ => Iff.rfl⟩
    intro _
    exact ⟨fun _ _ => True, fun _ _ => False, trivial, fun h => h⟩
  · refine ⟨fun E s => E Agent.first s, ?_, ?_⟩
    · intro _
      exact ⟨fun _ _ => True, fun _ _ => False, trivial, fun h => h⟩
    · refine ⟨fun _ s => s = Sentence.logical, fun hC => ?_⟩
      have h := (hC Sentence.logical Sentence.taste).1 rfl
      cases h

/-- `Unit` with the identity and the empty relation. -/
theorem undifferentiatedStructureModel : UndifferentiatedStructureModel :=
  ⟨PropositionalCollapse.noGlobalPropositionalCollapse,
    Unit, id, fun _ _ => False, ⟨()⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ h => h⟩

/-- Three values with a fixed middle under negation; the failing value alone is
not designated. -/
inductive Glut where
  | t | b | f

/-- Negation swaps the outer values and fixes the middle. -/
def Glut.neg : Glut → Glut
  | .t => .f
  | .b => .b
  | .f => .t

/-- The designated values. -/
def Glut.holds : Glut → Prop
  | .f => False
  | _ => True

theorem glutModel : GlutModel := by
  refine ⟨Glut, Glut.holds, Glut.neg, ⟨.b, trivial, trivial⟩, ⟨.f, fun h => h⟩, ?_, ?_, ?_⟩
  · intro p
    cases p
    · exact Or.inl trivial
    · exact Or.inl trivial
    · exact Or.inr trivial
  · intro h
    exact h .b trivial trivial
  · intro hC
    exact (hC .t .f).1 trivial

theorem collapseHornModels : CollapseHornModels := by
  refine ⟨⟨Bool, fun _ => True, not, ⟨true⟩, fun _ => trivial, fun _ => Or.inl trivial, ?_⟩,
    ⟨Bool, fun _ => False, not, ⟨true⟩, fun _ h => h, fun _ h => h.elim, ?_⟩⟩
  · intro h
    exact h true trivial trivial
  · intro h
    cases h true with
    | inl h => exact h
    | inr h => exact h

/-- Contents that track a Lean proposition for every agent, and one content true
for one agent only. -/
inductive RelativeContent where
  | logical (P : Prop)
  | perspectival

/-- Nothing is absolutely true; relative truth reads the content. -/
def relativeSemantics : TruthSemantics Bool RelativeContent where
  trueAbs := fun _ => False
  trueFor := fun a c =>
    match c with
    | .logical P => P
    | .perspectival => a = true

theorem relativeSurvivorModel : RelativeSurvivorModel := by
  have hExpr : ∀ b, Expressive (relativeSemantics.trueFor b) :=
    fun _ P => ⟨.logical P, Iff.rfl⟩
  refine ⟨RelativeContent, relativeSemantics, .perspectival, true, fun _ h => h,
    fun h => h.elim, fun hCapture => hCapture (fun _ h => h), hExpr,
    fun b => not_collapse_of_expressive (hExpr b), rfl, ?_⟩
  intro h
  cases h

theorem totalNihilistModel : TotalNihilistModel :=
  ⟨Bool, ⟨fun _ => False, fun _ _ => False⟩, not, ⟨true⟩, ⟨fun _ h => h, fun _ _ h => h⟩,
    fun _ h => h.elim⟩

/-- Only `false` is absolutely true; the thesis is `true`. -/
theorem thesisSchemaModel : ThesisSchemaModel := by
  refine ⟨Bool, ⟨fun p => p = false, fun _ _ => False⟩, true, false, ?_, ?_, ?_, rfl⟩
  · intro h
    cases h
  · intro hG
    exact (hG false rfl).elim
  · intro h
    cases h

/-- All eight controls. -/
theorem truthCollapseControls : TruthCollapseControls :=
  ⟨localCollapseModel, profileVariationModels, undifferentiatedStructureModel, glutModel,
    collapseHornModels, relativeSurvivorModel, totalNihilistModel, thesisSchemaModel⟩
end TruthCore.Results.Logic.TruthNontriviality.Controls
