import TruthCore.Models.Order
import TruthCore.Results.Logic.MaximumOrderSchema.Solution
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaFork

/-! Joint controls for a degree-order fork. `FiniteTop` reuses the registered
Boolean homogeneous causal control unchanged. `Unbounded` has natural-number
degrees and no causal edges: degree ascent is not a causal chain. Both have
actual strict comparisons. The single Unit respect is a fixture assignment;
it does not identify being, goodness, truth or nobility in the source.

Model assignments frozen before their joint witness certificates. These
interpretations concern encoded satisfiability, not metaphysical possibility.
The Nat control is infinite and must not enter the finite-model registry. -/
namespace TruthCore.Models.QuartaViaDegreeFork
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics

namespace FiniteTop
abbrev model := TruthCore.Models.Order.HomogeneousCausalControl.model
abbrev order := TruthCore.Models.Order.HomogeneousCausalControl.beingOrder

/-- The same registered two-being interpretation jointly satisfies the entire
nonlogical fork background and the strict causal-top branch. Named perfections
are all assigned the sole fixture respect; no source identity is claimed. -/
def JointWitness : Prop :=
  @HomogeneousScaleReading Bool Unit order model.InAct model.MoreIn model.esse ∧
  MaximumInBeingCausesAllBeingsReading model.InAct model.MoreIn model.CausesIn model.esse ∧
  CauseOfQualityInAnotherIsMoreSuchReading model.CausesIn model.MoreIn ∧
  GradesFoundInThingsReading model.MoreIn model.esse model.esse model.esse ∧
  QuartaViaStrictCausalTop model.InAct model.MoreIn model.CausesIn model.esse

theorem grades :
    GradesFoundInThingsReading model.MoreIn model.esse model.esse model.esse := by
  dsimp only [GradesFoundInThingsReading, model,
    TruthCore.Models.Order.HomogeneousCausalControl.model]
  decide

theorem gradesHaveMaximum :
    GradesByApproachToAMaximumReading model.InAct model.MoreIn := by
  dsimp only [GradesByApproachToAMaximumReading, IsMaximumIn, model,
    TruthCore.Models.Order.HomogeneousCausalControl.model]
  decide

theorem strictTop :
    QuartaViaStrictCausalTop model.InAct model.MoreIn model.CausesIn model.esse := by
  dsimp only [QuartaViaStrictCausalTop, IsMaximumIn, model,
    TruthCore.Models.Order.HomogeneousCausalControl.model]
  decide

theorem notUnbounded : ¬ QuartaViaUnboundedDegrees model.MoreIn model.esse := by
  dsimp only [QuartaViaUnboundedDegrees, model,
    TruthCore.Models.Order.HomogeneousCausalControl.model]
  decide

theorem fork : QuartaViaDegreeFork model.InAct model.MoreIn model.CausesIn model.esse :=
  ⟨⟨true, trivial⟩, Or.inl strictTop⟩

theorem jointWitness : JointWitness :=
  ⟨TruthCore.Models.Order.HomogeneousCausalControl.evaluation10,
    TruthCore.Models.Order.HomogeneousCausalControl.evaluation4,
    TruthCore.Models.Order.HomogeneousCausalControl.evaluation7, grades, strictTop⟩
end FiniteTop

namespace Unbounded
abbrev order : Preorder Nat := inferInstance
def inAct (_ : Nat) (_ : Unit) : Prop := True
def moreIn (_ : Unit) (x y : Nat) : Prop := y < x
def causesIn (_ _ : Nat) (_ : Unit) : Prop := False
def esse : Unit := ()

/-- Natural-number degrees jointly satisfy the same background and the
unbounded-degree branch, while there are no causal edges and no strict causal
top. The genus conditional is vacuous because no maximal member exists. -/
def JointWitness : Prop :=
  @HomogeneousScaleReading Nat Unit order inAct moreIn esse ∧
  MaximumInBeingCausesAllBeingsReading inAct moreIn causesIn esse ∧
  CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn ∧
  GradesFoundInThingsReading moreIn esse esse esse ∧
  QuartaViaUnboundedDegrees moreIn esse ∧
  (∀ c x, ¬ causesIn c x esse) ∧
  ¬ QuartaViaStrictCausalTop inAct moreIn causesIn esse

theorem scale : @HomogeneousScaleReading Nat Unit order inAct moreIn esse :=
  ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

/-- Reuse the existing no-maximum Nat control through the exact scale bridge. -/
theorem noMaximum : ¬ ∃ m, IsMaximumIn inAct moreIn esse m := by
  intro ⟨m, hm⟩
  exact TruthCore.Results.Logic.MaximumOrderSchema.maximumNeedNotExist
    ⟨m, (scale.isMaximumIn_iff_isMax m).mp hm⟩

theorem genus : MaximumInBeingCausesAllBeingsReading inAct moreIn causesIn esse :=
  fun m hm => (noMaximum ⟨m, hm⟩).elim

theorem causeMore : CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn :=
  fun _ _ _ _ h => h.elim

theorem grades : GradesFoundInThingsReading moreIn esse esse esse :=
  ⟨⟨1, 0, Nat.zero_lt_succ 0⟩, ⟨1, 0, Nat.zero_lt_succ 0⟩,
    ⟨1, 0, Nat.zero_lt_succ 0⟩⟩

theorem violatesGradesHaveMaximum :
    ¬ GradesByApproachToAMaximumReading inAct moreIn :=
  fun h => noMaximum (h esse ⟨1, 0, Nat.zero_lt_succ 0⟩)

theorem unboundedDegrees : QuartaViaUnboundedDegrees moreIn esse :=
  fun x => ⟨x + 1, Nat.lt_succ_self x⟩

theorem noCausalEdges : ∀ c x, ¬ causesIn c x esse := fun _ _ h => h

theorem notStrictTop : ¬ QuartaViaStrictCausalTop inAct moreIn causesIn esse :=
  fun ⟨m, hm, _⟩ => noMaximum ⟨m, hm⟩

theorem fork : QuartaViaDegreeFork inAct moreIn causesIn esse :=
  ⟨⟨0, trivial⟩, Or.inr unboundedDegrees⟩

/-- There is no causal series here, despite the strictly unbounded degrees. -/
theorem noCausalSeries :
    ¬ ∃ f : Nat → Nat, ∀ n, causesIn (f (n + 1)) (f n) esse :=
  fun ⟨_, h⟩ => h 0

theorem jointWitness : JointWitness :=
  ⟨scale, genus, causeMore, grades, unboundedDegrees, noCausalEdges, notStrictTop⟩
end Unbounded

/-- Two independently specified joint interpretations of the fork's entire
nonlogical background. This does not select either branch as metaphysically
true or make the infinite interpretation a finite registered model. -/
def BranchWitnesses : Prop := FiniteTop.JointWitness ∧ Unbounded.JointWitness

theorem branchWitnesses : BranchWitnesses :=
  ⟨FiniteTop.jointWitness, Unbounded.jointWitness⟩

/-! The empty-domain control is deliberately separate from the nonempty branch
witnesses above. It is not a member of the finite-model registry. -/
namespace EmptyControl
def inAct (_ : Empty) (_ : Unit) : Prop := False
def moreIn (_ : Unit) (_ _ : Empty) : Prop := False
def esse : Unit := ()

theorem gradesHaveMaximum : GradesByApproachToAMaximumReading inAct moreIn := by
  intro _ ⟨x, _, _⟩
  exact Empty.elim x

theorem unboundedDegrees : QuartaViaUnboundedDegrees moreIn esse :=
  fun x => Empty.elim x

theorem violatesGradesFound : ¬ GradesFoundInThingsReading moreIn esse esse esse := by
  intro ⟨⟨x, _, _⟩, _, _⟩
  exact Empty.elim x
end EmptyControl

end TruthCore.Models.QuartaViaDegreeFork
