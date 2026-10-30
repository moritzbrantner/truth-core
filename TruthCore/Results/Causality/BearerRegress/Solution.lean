import TruthCore.Causality.BearerRegress
import TruthCore.Results.Logic.CogitoSubject.Solution

namespace TruthCore.Results.Causality.BearerRegress

open TruthCore.Causality.BearerRegress
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Greek.Aristotle.Categories (PrimarySubstanceBySubjectRelationsReading)
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Logic (ExcludedMiddle)

section General

variable {W B Episode : Type}

theorem acc_of_ancestor {m : Ontic W B} {R : W → B → B → Prop} {w : W} {x b : B}
    (hAcc : Acc (PresentEsseSupport m R w) b) (hAnc : SupportAncestor m R w x b) :
    Acc (PresentEsseSupport m R w) x := by
  induction hAnc using Relation.ReflTransGen.head_induction_on with
  | refl => exact hAcc
  | head hEdge _ ih => exact ih.inv hEdge

/-- Descent to a terminus below any accessible existing ancestor. -/
theorem terminus_of_acc {m : Ontic W B} {R : W → B → B → Prop} {Dependent : B → Prop} {w : W}
    {Occurs : Episode → Prop} {Bears : B → Episode → Prop} {b : B} {e : Episode}
    (hOcc : Occurs e) (hBears : Bears b e)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hEM : ExcludedMiddle) :
    ∀ x, Acc (PresentEsseSupport m R w) x → SupportAncestor m R w x b → m.ExistsAt w x →
      ∃ t, SupportTerminus m R Dependent w b t := by
  intro x hAcc
  induction hAcc with
  | intro x _ ih =>
    intro hAnc hEx
    cases hEM (∃ c, PresentEsseSupport m R w c x) with
    | inl h =>
      obtain ⟨c, hc⟩ := h
      exact ih c hc (Relation.ReflTransGen.head hc hAnc) hc.1
    | inr h =>
      refine ⟨x, hAnc, hEx, fun c hc hR => h ⟨c, hc, hR⟩, fun hDep => ?_⟩
      exact h (hAncestry b e x hOcc hBears hAnc hEx hDep)

/-- A non-accessible bearer has an endless ancestor set. -/
theorem endless_of_not_acc {m : Ontic W B} {R : W → B → B → Prop} {w : W} {b : B}
    (hEM : ExcludedMiddle) (hNot : ¬ Acc (PresentEsseSupport m R w) b) :
    EndlessSupportBelow m R w b := by
  refine ⟨fun x => SupportAncestor m R w x b ∧ ¬ Acc (PresentEsseSupport m R w) x,
    ⟨Relation.ReflTransGen.refl, hNot⟩, ?_⟩
  rintro x ⟨hAnc, hx⟩
  refine ⟨hAnc, ?_⟩
  cases hEM (∃ y, PresentEsseSupport m R w y x ∧ ¬ Acc (PresentEsseSupport m R w) y) with
  | inl h =>
    obtain ⟨y, hy, hyNot⟩ := h
    exact ⟨y, ⟨Relation.ReflTransGen.head hy hAnc, hyNot⟩, hy⟩
  | inr h =>
    refine absurd (Acc.intro x fun y hy => ?_) hx
    cases hEM (Acc (PresentEsseSupport m R w) y) with
    | inl hy' => exact hy'
    | inr hy' => exact absurd ⟨y, hy, hy'⟩ h

theorem not_endless_of_acc {m : Ontic W B} {R : W → B → B → Prop} {w : W} {b : B}
    (hAcc : Acc (PresentEsseSupport m R w) b) : ¬ EndlessSupportBelow m R w b := by
  rintro ⟨S, hb, hS⟩
  have key : ∀ x, Acc (PresentEsseSupport m R w) x → ¬ S x := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro hSx
      obtain ⟨_, y, hSy, hy⟩ := hS x hSx
      exact ih y hy hSy
  exact key b hAcc hb

/-- A support cycle below `b` gives an endless ancestor set: the ancestors of `b`
that lie downstream of the cycle. -/
theorem endless_of_cycle {m : Ontic W B} {R : W → B → B → Prop} {w : W} {b : B}
    (h : SupportCycleBelow m R w b) : EndlessSupportBelow m R w b := by
  obtain ⟨x, hAnc, hCyc⟩ := h
  refine ⟨fun y => Relation.ReflTransGen (PresentEsseSupport m R w) x y ∧
    SupportAncestor m R w y b, ⟨hAnc, Relation.ReflTransGen.refl⟩, ?_⟩
  rintro y ⟨hxy, hyb⟩
  refine ⟨hyb, ?_⟩
  cases hxy with
  | refl =>
    obtain ⟨z, hxz, hzx⟩ := Relation.TransGen.tail'_iff.mp hCyc
    exact ⟨z, ⟨hxz, Relation.ReflTransGen.head hzx hyb⟩, hzx⟩
  | tail hxz hzy =>
    exact ⟨_, ⟨hxz, Relation.ReflTransGen.head hzy hyb⟩, hzy⟩

theorem not_cycle_of_acc {m : Ontic W B} {R : W → B → B → Prop} {w : W} {b : B}
    (hAcc : Acc (PresentEsseSupport m R w) b) : ¬ SupportCycleBelow m R w b :=
  fun h => not_endless_of_acc hAcc (endless_of_cycle h)

theorem bearerOutcome {m : Ontic W B} {R : W → B → B → Prop} {Dependent : B → Prop}
    (Substance : B → Prop) {w : W}
    {Occurs : Episode → Prop} {Bears : B → Episode → Prop} {b : B} {e : Episode}
    (hOcc : Occurs e) (hBears : Bears b e)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hEM : ExcludedMiddle) :
    BearerOutcome m R Dependent Substance w b := by
  cases hEM (Acc (PresentEsseSupport m R w) b) with
  | inl hAcc =>
    obtain ⟨t, ht⟩ := terminus_of_acc hOcc hBears hAncestry hEM b hAcc
      Relation.ReflTransGen.refl (hExists b e hOcc hBears)
    cases hEM (Substance t) with
    | inl hs => exact Or.inl ⟨hAcc, t, ht, hs⟩
    | inr hs => exact Or.inr (Or.inl ⟨hAcc, t, ht, hs⟩)
  | inr hNot =>
    cases hEM (SupportCycleBelow m R w b) with
    | inl hc => exact Or.inr (Or.inr (Or.inl hc))
    | inr hc => exact Or.inr (Or.inr (Or.inr ⟨endless_of_not_acc hEM hNot, hc⟩))

/-- Coverage only: some bearer of an occurring thought has a terminus satisfying
`Substance`, a terminus failing it, a support cycle below it, or an acyclic
endless ancestry. -/
theorem someBearerOutcome
    (m : Ontic W B) (R : W → B → B → Prop) (Dependent Substance : B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hEM : ExcludedMiddle) :
    SomeBearerOutcome m R Dependent Substance Occurs Bears w := by
  obtain ⟨b, e, hOcc, hBears⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  exact ⟨b, e, hOcc, hBears, bearerOutcome Substance hOcc hBears hExists hAncestry hEM⟩

/-- The conditional independent-terminus lemma: well-foundedness eliminates the
nonterminating branches. No substance predicate is involved. -/
theorem terminusOfWellFounded
    (m : Ontic W B) (R : W → B → B → Prop) (Dependent : B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hWF : WellFoundedPresentEsseSupport m R w)
    (hEM : ExcludedMiddle) :
    ∃ b e x, Occurs e ∧ Bears b e ∧ SupportTerminus m R Dependent w b x := by
  obtain ⟨b, e, hOcc, hBears⟩ :=
    TruthCore.Results.Logic.CogitoSubject.thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  obtain ⟨t, ht⟩ := terminus_of_acc hOcc hBears hAncestry hEM b (hWF.apply b)
    Relation.ReflTransGen.refl (hExists b e hOcc hBears)
  exact ⟨b, e, t, hOcc, hBears, ht⟩

/-- With actual support well-founded and both subject relations yielding existing
support, some bearer of an occurring thought has a terminus that passes the
*Categories* negative primary-substance test. -/
theorem primarySubstanceTerminus
    (m : Ontic W B) (R : W → B → B → Prop) (Dependent IsPrimarySubstance : B → Prop)
    (SaidOf In : B → B → Prop)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop) (w : W)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hExists : EveryBearerExistsAt m Occurs Bears w)
    (hAncestry : BearerAncestryDependentsSupported m R Dependent Occurs Bears w)
    (hWF : WellFoundedPresentEsseSupport m R w)
    (hReading : PrimarySubstanceBySubjectRelationsReading IsPrimarySubstance SaidOf In)
    (hIn : InSubjectIsExistentSupport m R In w)
    (hSaidOf : SaidOfSubjectIsExistentSupport m R SaidOf w)
    (hEM : ExcludedMiddle) :
    PrimarySubstanceTerminusOfBearer m R Dependent IsPrimarySubstance Occurs Bears w := by
  obtain ⟨b, e, x, hOcc, hBears, ht⟩ :=
    terminusOfWellFounded m R Dependent Occurs Bears w hOccurs hBearer hExists hAncestry hWF hEM
  refine ⟨b, e, x, hOcc, hBears, ht, (hReading x).2 ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨hyEx, hR⟩ := hSaidOf x y ht.2.1 hy
    exact ht.2.2.1 y hyEx hR
  · rintro ⟨y, hy⟩
    obtain ⟨hyEx, hR⟩ := hIn x y ht.2.1 hy
    exact ht.2.2.1 y hyEx hR

theorem outcomeExclusions : OutcomeExclusions := by
  intro _ _ m R _ _ w b hTerm hNon
  have hAcc : Acc (PresentEsseSupport m R w) b := by
    rcases hTerm with h | h <;> exact h.1
  rcases hNon with h | h
  · exact not_cycle_of_acc hAcc h
  · exact not_endless_of_acc hAcc h.1

/-- No terminus below `b` when the supplied set of ancestors all have supporters. -/
theorem no_terminus_of_supported {m : Ontic W B} {R : W → B → B → Prop} {Dep : B → Prop}
    {w : W} {b : B} (h : ∀ x, ∃ c, PresentEsseSupport m R w c x) :
    ¬ ∃ x, SupportTerminus m R Dep w b x := by
  rintro ⟨x, _, _, hNo, _⟩
  obtain ⟨c, hc, hR⟩ := h x
  exact hNo c hc hR

end General

/-! ## Controls -/

theorem emptyWF {B : Type} : WellFoundedPresentEsseSupport (oneWorld B)
    (fun _ _ _ => False) () :=
  ⟨fun _ => Acc.intro _ fun _ h => h.2.elim⟩

theorem anc_of_empty {B : Type} {x b : B}
    (h : SupportAncestor (oneWorld B) (fun _ _ _ => False) () x b) : x = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hEdge _ _ => exact hEdge.2.elim

theorem emptyAcc {B : Type} (b : B) :
    Acc (PresentEsseSupport (oneWorld B) (fun _ _ _ => False) ()) b :=
  emptyWF.apply b

theorem substanceBranch : SubstanceBranchModel := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial, ?_⟩,
    emptyWF, ⟨emptyAcc (), (), ⟨Relation.ReflTransGen.refl, trivial, fun _ _ h => h, id⟩, trivial⟩, ?_⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · rintro ⟨_, _, _, h⟩
    exact h trivial

theorem nonSubstanceBranch : NonSubstanceBranchModel := by
  refine ⟨⟨⟨true, rfl⟩, fun e he => ⟨false, rfl, he⟩, fun _ _ _ _ => trivial, ?_⟩,
    emptyWF, ⟨emptyAcc false, false, ⟨Relation.ReflTransGen.refl, trivial, fun _ _ h => h, id⟩, id⟩,
    ?_, ?_, ⟨rfl, rfl⟩, fun _ _ h => h⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · rintro ⟨_, _, _, h⟩
    exact h
  · rintro ⟨_, _, h⟩
    cases h

theorem cycleEdge {c b : Bool} (h : c ≠ b) :
    PresentEsseSupport (oneWorld Bool) cycleSupport () c b := ⟨trivial, h⟩

theorem cycleBranch : CycleBranchModel := by
  have hFT := cycleEdge (c := false) (b := true) (by decide)
  have hTF := cycleEdge (c := true) (b := false) (by decide)
  have hSup : ∀ x : Bool, ∃ c, PresentEsseSupport (oneWorld Bool) cycleSupport () c x := by
    intro x
    cases x
    · exact ⟨true, hTF⟩
    · exact ⟨false, hFT⟩
  have hCyc : SupportCycleBelow (oneWorld Bool) cycleSupport () false :=
    ⟨false, Relation.ReflTransGen.refl,
      Relation.TransGen.head hFT (Relation.TransGen.single hTF)⟩
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨false, rfl⟩, fun _ _ _ _ => trivial, ?_⟩, hCyc, ?_,
    no_terminus_of_supported hSup⟩
  · intro _ _ x _ _ _ _ _
    exact hSup x
  · intro hWF
    exact not_cycle_of_acc (hWF.apply false) hCyc

theorem chainEdge (n : Nat) :
    PresentEsseSupport (oneWorld Nat) chainSupport () (n + 1) n := ⟨trivial, rfl⟩

theorem chainAnc (n : Nat) : SupportAncestor (oneWorld Nat) chainSupport () n 0 := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact Relation.ReflTransGen.head (chainEdge n) ih

theorem chain_lt {x y : Nat}
    (h : Relation.TransGen (PresentEsseSupport (oneWorld Nat) chainSupport ()) x y) : y < x := by
  induction h with
  | single hEdge =>
    have : _ = _ := hEdge.2
    omega
  | tail _ hEdge ih =>
    have : _ = _ := hEdge.2
    omega

theorem chainBranch : ChainBranchModel := by
  have hSup : ∀ x : Nat, ∃ c, PresentEsseSupport (oneWorld Nat) chainSupport () c x :=
    fun x => ⟨x + 1, chainEdge x⟩
  have hEnd : EndlessSupportBelow (oneWorld Nat) chainSupport () 0 :=
    ⟨fun _ => True, trivial, fun x _ => ⟨chainAnc x, x + 1, trivial, chainEdge x⟩⟩
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨0, rfl⟩, fun _ _ _ _ => trivial, ?_⟩,
    ⟨hEnd, ?_⟩, ?_, no_terminus_of_supported hSup⟩
  · intro _ _ x _ _ _ _ _
    exact hSup x
  · rintro ⟨x, _, hc⟩
    exact absurd (chain_lt hc) (Nat.lt_irrefl x)
  · intro hWF
    exact not_endless_of_acc (hWF.apply 0) hEnd

theorem bundleEdge {c b : BundleNode} (h : bundleSupport () c b) :
    PresentEsseSupport (oneWorld BundleNode) bundleSupport () c b := ⟨trivial, h⟩

theorem bundleCycle : BundleCycleModel := by
  have hLB := bundleEdge (c := .left) (b := .bundle) trivial
  have hRB := bundleEdge (c := .right) (b := .bundle) trivial
  have hLR := bundleEdge (c := .left) (b := .right) trivial
  have hRL := bundleEdge (c := .right) (b := .left) trivial
  refine ⟨⟨⟨.thought, rfl⟩, fun e he => ⟨.bundle, rfl, he⟩, fun _ _ _ _ => trivial, ?_⟩,
    ⟨.left, Relation.ReflTransGen.single hLB,
      Relation.TransGen.head hLR (Relation.TransGen.single hRL)⟩, ?_, ?_⟩
  · rintro _ _ x _ _ _ _ (rfl | rfl | rfl)
    · exact ⟨_, hLB⟩
    · exact ⟨_, hRL⟩
    · exact ⟨_, hLR⟩
  · intro h
    obtain ⟨c, hEdge, _⟩ := Relation.TransGen.head'_iff.mp h
    cases c <;> exact hEdge.2.elim
  · rintro ⟨_, _, h⟩
    cases h

theorem rootsEdge {c : Fin 3} (h : c ≠ 0) :
    PresentEsseSupport (oneWorld (Fin 3)) rootsSupport () c 0 := ⟨trivial, rfl, h⟩

theorem bothTermini : BothTerminiModel := by
  have hLeaf : ∀ x : Fin 3, x ≠ 0 →
      Acc (PresentEsseSupport (oneWorld (Fin 3)) rootsSupport ()) x :=
    fun x hx => Acc.intro x fun _ h => absurd h.2.1 hx
  have hAcc0 : Acc (PresentEsseSupport (oneWorld (Fin 3)) rootsSupport ()) 0 :=
    Acc.intro 0 fun y h => hLeaf y h.2.2
  have hTerm : ∀ x : Fin 3, x ≠ 0 →
      SupportTerminus (oneWorld (Fin 3)) rootsSupport (fun x => x = 0) () 0 x :=
    fun x hx => ⟨Relation.ReflTransGen.single (rootsEdge hx), trivial,
      fun _ _ h => hx h.1, hx⟩
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨0, rfl⟩, fun _ _ _ _ => trivial, ?_⟩, ?_,
    ⟨hAcc0, 1, hTerm 1 (by decide), rfl⟩, ⟨hAcc0, 2, hTerm 2 (by decide), by decide⟩⟩
  · rintro _ _ x _ _ _ _ rfl
    exact ⟨1, rootsEdge (by decide)⟩
  · refine ⟨fun x => ?_⟩
    by_cases hx : x = 0
    · exact hx ▸ hAcc0
    · exact hLeaf x hx

theorem mixedEdge {c b : Fin 3} (h : mixedSupport () c b) :
    PresentEsseSupport (oneWorld (Fin 3)) mixedSupport () c b := ⟨trivial, h⟩

theorem terminusWithCycle : TerminusWithCycleModel := by
  have h10 := mixedEdge (c := 1) (b := 0) (Or.inl ⟨rfl, rfl⟩)
  have h20 := mixedEdge (c := 2) (b := 0) (Or.inr ⟨rfl, Or.inl rfl⟩)
  have h22 := mixedEdge (c := 2) (b := 2) (Or.inr ⟨rfl, Or.inr rfl⟩)
  have hSplit : ∀ x : Fin 3, x ≠ 1 → x = 0 ∨ x = 2 := by decide
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨0, rfl⟩, fun _ _ _ _ => trivial, ?_⟩, ⟨1, ?_⟩,
    ⟨2, Relation.ReflTransGen.single h20, Relation.TransGen.single h22⟩⟩
  · intro _ _ x _ _ _ _ hDep
    rcases hSplit x hDep with rfl | rfl
    · exact ⟨_, h10⟩
    · exact ⟨_, h22⟩
  · refine ⟨Relation.ReflTransGen.single h10, trivial, ?_, fun h => h rfl⟩
    rintro c _ (⟨_, h⟩ | ⟨_, h | h⟩) <;> exact absurd h (by decide)

theorem omitAncestryPremise : OmitAncestryPremiseModel := by
  refine ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial, emptyWF, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, hR⟩ := h () () () trivial trivial Relation.ReflTransGen.refl trivial trivial
    exact hR
  · rintro ⟨_, _, _, _, h⟩
    exact h trivial

theorem contingentTerminus : ContingentTerminusModel := by
  have hWF : WellFoundedPresentEsseSupport contingentOntic (fun _ _ _ => False) false :=
    ⟨fun _ => Acc.intro _ fun _ h => h.2.elim⟩
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => rfl, ?_⟩, hWF,
    ⟨hWF.apply (), (), ⟨Relation.ReflTransGen.refl, rfl, fun _ _ h => h, id⟩, trivial⟩,
    ⟨rfl, true, trivial, by simp [contingentOntic]⟩, fun h => ?_⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · have : true = false := h true trivial
    cases this

theorem omitInBridge : OmitInBridgeModel := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨false, rfl⟩, fun _ _ _ _ => trivial, ?_⟩, emptyWF, ?_,
    fun _ _ _ h => h.elim, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · intro x
    cases x
    · refine ⟨fun h => Bool.noConfusion h, fun h => absurd ⟨true, rfl, rfl⟩ h.2⟩
    · refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => rfl⟩
      · rintro ⟨_, h⟩
        exact h
      · rintro ⟨_, h, _⟩
        exact Bool.noConfusion h
  · intro h
    exact (h false true trivial ⟨rfl, rfl⟩).2
  · rintro ⟨b, _, x, _, rfl, ⟨hAnc, _⟩, hPS⟩
    have : x = false := anc_of_empty hAnc
    subst this
    cases hPS

theorem omitSaidOfBridge : OmitSaidOfBridgeModel := by
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨false, rfl⟩, fun _ _ _ _ => trivial, ?_⟩, emptyWF, ?_,
    fun _ _ _ h => h.elim, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · intro x
    cases x
    · refine ⟨fun h => Bool.noConfusion h, fun h => absurd ⟨true, rfl, rfl⟩ h.1⟩
    · refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => rfl⟩
      · rintro ⟨_, h, _⟩
        exact Bool.noConfusion h
      · rintro ⟨_, h⟩
        exact h
  · intro h
    exact (h false true trivial ⟨rfl, rfl⟩).2
  · rintro ⟨b, _, x, _, rfl, ⟨hAnc, _⟩, hPS⟩
    have : x = false := anc_of_empty hAnc
    subst this
    cases hPS

theorem negativeTest : NegativeTestControl := by
  have hTerm : SupportTerminus (oneWorld Unit) (fun _ _ _ => False) (fun _ => False) () () () :=
    ⟨Relation.ReflTransGen.refl, trivial, fun _ _ h => h, id⟩
  refine ⟨⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial, ?_⟩, emptyWF, ?_,
    fun _ _ _ h => h.elim, fun _ _ _ h => h.elim,
    ⟨(), (), (), trivial, trivial, hTerm, trivial⟩, ⟨emptyAcc (), (), hTerm, id⟩⟩
  · intro _ _ _ _ _ _ _ hDep
    exact hDep.elim
  · intro _
    exact ⟨fun _ => ⟨fun ⟨_, h⟩ => h, fun ⟨_, h⟩ => h⟩, fun _ => trivial⟩

/-- The branch witnesses, omission models and exclusions. -/
theorem controls : BearerRegressControls :=
  ⟨substanceBranch, nonSubstanceBranch, cycleBranch, chainBranch, bundleCycle, bothTermini,
    terminusWithCycle, omitAncestryPremise, contingentTerminus, omitInBridge, omitSaidOfBridge,
    negativeTest, outcomeExclusions⟩

end TruthCore.Results.Causality.BearerRegress
