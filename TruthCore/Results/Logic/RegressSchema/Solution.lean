import TruthCore.Logic.RegressDomains

namespace TruthCore.Results.Logic.RegressSchema
open TruthCore.Logic.Regress TruthCore.Logic.RegressDomains TruthCore.Causality

theorem structural : StructuralSchema :=
  ⟨fun _ G h => G.controls_of_wellFounded h,
    fun _ _ _ _ f h => f.wellFounded h,
    fun _ G intrinsic => G.grounded_eq_lfp intrinsic,
    fun _ G intrinsic h => G.fixedPoints_equal_of_wellFounded intrinsic h⟩

theorem efficientTransfer : EfficientTransfer := by
  intro B cause perSe hf hl hi
  exact (efficient perSe).controls_of_wellFounded
    ⟨TruthCore.Results.Case.Catholicism.CausalFinitism.perSeNoRegressOfFiniteAncestry
      cause perSe hf hl hi⟩

theorem motionTransfer : MotionTransfer := by
  intro B R MovedIn MovesIn MovesAsMoved hi hp hw
  exact (motion MovesIn).controls_of_wellFounded
    ⟨TruthCore.Results.Aristotle.Physics.Typed.MovedByAnotherRegressFromPerSeRegress.movedByAnotherRegressFromPerSeRegress MovedIn MovesIn MovesAsMoved hi hp hw⟩

theorem groundingTransfer : GroundingTransfer := by
  intro E Q F e intrinsic hg hs hu
  exact (grounding e).controls_of_wellFounded
    ⟨TruthCore.Results.Causality.GroundingYieldsRegress.groundingWithUniqueCauseYieldsRegressReading _ e.Grounds intrinsic hg hs hu⟩

theorem explanationTransfer : ExplanationTransfer := by
  intro W B R e w lower rank hw hr
  let f : (explanation e w).Map (⟨lower⟩ : Graph R) :=
    ⟨rank, fun ⟨r, hExplains, hRequires⟩ => hr r _ _ hExplains hRequires⟩
  exact (explanation e w).controls_of_wellFounded (f.wellFounded hw)

theorem parthoodTransfer : ParthoodTransfer := by
  intro P ord hw
  exact (parthood P).controls_of_wellFounded hw

/-- Induction uses ALL premise warrants. Nonempty rules allow extraction of
one finite branch; this is a necessary path condition, never its converse. -/
theorem justificationTransfer : JustificationTransfer := by
  intro C j c nonempty hc
  induction hc with
  | foundation c hf => exact ⟨c, .same c, hf⟩
  | inference r _ ih =>
    obtain ⟨p, hp⟩ := nonempty r
    obtain ⟨s, path, hs⟩ := ih p hp
    exact ⟨s, .link ⟨r, rfl, hp⟩ path, hs⟩

private theorem epistemicBridge : EpistemicBridge := by
  intro B C causal j bridge hw
  exact causal.controls_of_wellFounded (bridge.wellFounded hw)

private def infiniteJustification : Justification Nat where
  Rule := Nat
  premise r p := p = r + 1
  conclusion r := r
  noninferential _ := False
  justified _ := False

private theorem infiniteUnwarranted : ∀ n, ¬ GeneratedWarrant infiniteJustification n := by
  intro n hn
  induction hn with
  | foundation _ hf => exact hf
  | inference r _ ih => exact ih (Nat.succ r) rfl

private theorem crossDomainBoundary : CrossDomainBoundary := by
  let G : Graph Nat := ⟨SuccessorBorrowingLink⟩
  have noFG : ∀ x, ¬ FinitelyGroundedPower G.edge (fun _ => False) x := by
    intro x hx
    obtain ⟨_, _, hf⟩ := TruthCore.Results.Causality.FiniteGroundingHasSource.finiteGroundingHasSource Nat G.edge (fun _ => False) x hx
    exact hf
  refine ⟨G, infiniteJustification, (fun _ => True), (fun _ => True), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y x
    exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨r, hr, hp⟩ => hr ▸ hp⟩
  · intro x
    exact ⟨trivial, trivial, id, infiniteUnwarranted x⟩
  · intro x hs
    exact hs ⟨x + 1, rfl⟩
  · intro x
    exact ⟨fun _ => ⟨x + 1, rfl, trivial⟩, fun _ => trivial⟩
  · have on : (Set.univ : Set Nat) ⊆ (G.transmission (fun _ => False)).gfp := by
      apply (G.transmission (fun _ => False)).le_gfp
      intro x _
      exact Or.inr ⟨x + 1, rfl, trivial⟩
    exact on trivial
  · rw [← G.grounded_eq_lfp (fun _ => False)]
    exact noFG 0
  · intro hw
    exact ((G.controls_of_wellFounded hw).2.1) ⟨id, fun _ => rfl⟩

private theorem cycleAndConverseBoundary : CycleAndConverseBoundary := by
  let G : Graph Unit := ⟨fun _ _ => True⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro hw
    exact ((G.controls_of_wellFounded hw).1 ()) (.single trivial)
  · rintro ⟨s, hs⟩
    exact Nat.zero_ne_one (hs (Subsingleton.elim (s 0) (s 1)))
  · apply le_antisymm (G.transmission (fun _ => True)).lfp_le_gfp
    intro x _
    rw [← (G.transmission (fun _ => True)).map_lfp]
    exact Or.inl trivial

private theorem knowledgeSelfApplication : KnowledgeSelfApplication := by
  intro C j knows norm possibilityClaim hStandard hScope hFail
  exact TruthCore.Logic.SelfApplication.Norm.selfApplication hScope
    (fun h => hFail ((hStandard possibilityClaim).mp h))

private theorem atomlessBoundary : AtomlessBoundary := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨OrderDual.toDual (Nat.succ (OrderDual.ofDual x)), Nat.lt_succ_self _⟩
  · intro x
    exact Nat.lt_irrefl (OrderDual.ofDual x)
  · intro x y z hxy hyz
    exact Nat.lt_trans hyz hxy
  · intro hw
    obtain ⟨s, _, hs⟩ := ((parthood (OrderDual Nat)).controls_of_wellFounded hw).2.2
      (OrderDual.toDual 0)
    exact hs ⟨OrderDual.toDual (Nat.succ (OrderDual.ofDual s)), Nat.lt_succ_self _⟩

private theorem allPremiseBoundary : AllPremiseBoundary := by
  let j : Justification Bool :=
    { Rule := Unit
      premise := fun _ _ => True
      conclusion := fun _ => false
      noninferential := fun c => c = true
      justified := fun _ => False }
  refine ⟨j, (fun _ => ⟨true, trivial⟩), .link ⟨(), rfl, trivial⟩ (.same true), rfl, ?_⟩
  have onlyTrue : ∀ c, GeneratedWarrant j c → c = true := by
    intro c hc
    induction hc with
    | foundation c hf => exact hf
    | inference _ _ ih => exact Bool.noConfusion (ih false trivial)
  intro hf
  exact Bool.noConfusion (onlyTrue false hf)

private theorem sourceFreeSemanticBridge : SourceFreeSemanticBridge := by
  intro B C causal j active claimOf nonempty warrantBridge foundationBridge noSource x hx
  obtain ⟨p, _, hp⟩ := justificationTransfer C j (claimOf x) nonempty (warrantBridge x hx)
  obtain ⟨source, hs⟩ := foundationBridge p hp
  exact noSource source hs

/-- Analyst's shared structural schema, six separately typed conditional
transfers, and discriminating boundary controls. No actual philosophical
well-foundedness or epistemic-to-causal bridge is supplied. -/
theorem regressSchemaPackage : DomainPackage :=
  ⟨structural, efficientTransfer, motionTransfer, groundingTransfer,
    explanationTransfer, parthoodTransfer, justificationTransfer,
    epistemicBridge, crossDomainBoundary, cycleAndConverseBoundary,
    knowledgeSelfApplication, atomlessBoundary, allPremiseBoundary, sourceFreeSemanticBridge⟩

end TruthCore.Results.Logic.RegressSchema
