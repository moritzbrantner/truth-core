module

public import TruthCore.Explanation.GroundingBaseline
public import TruthCore.Logic.Configuration
public import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution
public import TruthCore.Results.Explanation.CondensationSufficiency.Solution

@[expose] public section
namespace TruthCore.Results.Explanation.GroundingBaseline
open TruthCore.Explanation.GroundingBaseline
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.Regress

private theorem shallowWF {X : Type} (R : X → X → Prop)
    (h : ∀ x y z, R x y → R y z → False) : WellFounded R :=
  ⟨fun z => Acc.intro z (fun y hy => Acc.intro y (fun x hx => (h x y z hx hy).elim))⟩

private theorem emptyWF {X : Type} : WellFounded (emptyR : X → X → Prop) :=
  ⟨fun x => Acc.intro x (fun _ h => h.elim)⟩

/-- Structural induction on the existing modal language; grounding never enters
its atomic interpretation. Accessibility and existence can be extensionally equal. -/
theorem modalInvariant {W B : Type} (M N : Extension W B) (h : SameModal M N)
    (p : TruthCore.Modal.Formula (ModalAtom B)) :
    ∀ w, ModalTruth M w p ↔ ModalTruth N w p := by
  induction p with
  | atom b =>
      intro w
      cases b with
      | inl b => exact h.2 w b
      | inr b => exact Iff.rfl
  | falsum => exact fun _ => Iff.rfl
  | imp p q ihp ihq =>
      intro w
      exact ⟨fun hp hpn => (ihq w).1 (hp ((ihp w).2 hpn)),
        fun hn hpm => (ihq w).2 (hn ((ihp w).1 hpm))⟩
  | box p ih =>
      intro w
      exact ⟨fun hm v hv => (ih v).1 (hm v ((h.1 w v).2 hv)),
        fun hn v hv => (ih v).2 (hn v ((h.1 w v).1 hv))⟩
  | diamond p ih =>
      intro w
      exact ⟨fun ⟨v, hv, hp⟩ => ⟨v, (h.1 w v).1 hv, (ih v).1 hp⟩,
        fun ⟨v, hv, hp⟩ => ⟨v, (h.1 w v).2 hv, (ih v).2 hp⟩⟩

theorem modalIndependence : ModalIndependence := by
  refine ⟨fun _ _ M N h w p => modalInvariant M N h p w,
    ⟨(fun _ _ => Iff.rfl), (fun _ _ => Iff.rfl)⟩, ?_, ?_, ?_, ?_,
    (fun _ _ => trivial), ?_, ?_, ?_⟩
  · intro _ _ _ h; exact h.elim
  · intro w r f h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inl rfl, Or.inr rfl, Bool.noConfusion⟩
  · intro _; exact emptyWF
  · intro w
    apply shallowWF
    intro x y z hxy hyz
    exact Bool.noConfusion (hxy.2.2.symm.trans hyz.2.1)
  · exact ⟨Or.inr rfl, true, trivial, fun h => h.elim Bool.noConfusion Bool.noConfusion⟩
  · exact fun ⟨_, h⟩ => h.elim
  · exact ⟨true, rfl, rfl, rfl⟩

/-- Consume the repository's normal-modal K theorem, without frame conditions. -/
theorem necessitationImpossible {W B F : Type} (A : Arena W B F) (a : W) (p q : F)
    (hc : Contingent A a p) (hn : NecessaryFact A a q)
    (hs : NecessaryImplication A a q p) : TruthCore.Logic.ConfigurationFalse := by
  have hp := TruthCore.Modal.axiomK_valid A.ontic.frame
    (.atom q) (.atom p) A.holds a hs hn
  obtain ⟨_, v, hv, hnot⟩ := hc
  exact hnot (hp v hv)

theorem necessitationCore : NecessitationCore := by
  refine ⟨fun _ _ _ A a p q hc hn hs => necessitationImpossible A a p q hc hn hs,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, v, _, hn⟩; exact hn trivial
  · intro _ _; trivial
  · intro _ _ _; trivial
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · exact fun h => Bool.noConfusion (h true trivial)
  · intro _ _ h; exact h
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · intro _ _; trivial
  · exact fun h => Bool.noConfusion (h true trivial trivial)

/-- The old forced-descent lemma is applied to an explicit R-reason projection.
No ReasonClosed/nonCopy/selected-full-ground witness is smuggled into the input. -/
theorem contingentTerminus {W B F : Type} (A : Arena W B F) (a : W)
    (R : F → F → Prop) (G : FullGround F) (x : F)
    (hEM : ExcludedMiddle) (hc : Contingent A a x) (hf : WellFounded R)
    (ha : ActualMembers A a G) (hl : LinkedMembers R G)
    (hn : JointNecessitation A a G) : UngroundedContingent A a G := by
  rcases hEM (UngroundedContingent A a G) with yes | no
  · exact yes
  · apply False.elim
    let V := reasonView A a R
    have found : TruthCore.Explanation.ExplanatoryAdequacy.Founded V a (fun _ => True) := by
      let f : Graph.Map
          ⟨TruthCore.Explanation.ExplanatoryAdequacy.ContingentReason V a (fun _ => True)⟩
          ⟨R⟩ := ⟨id, fun h => h.2.2.1.2⟩
      exact f.wellFounded hf
    apply TruthCore.Results.Explanation.ExplanatoryAdequacy.forced
      (A := V) (S := fun _ => True) True.intro hc found
    intro c _ hcc hNoCont
    rcases hEM (∃ S, G S c) with hFull | hNone
    · obtain ⟨S, hS⟩ := hFull
      obtain ⟨_, v, hv, hnot⟩ := hcc
      apply hnot
      apply hn S c hS v hv
      intro r hr
      rcases hEM (A.holds v r) with hTrue | hFalse
      · exact hTrue
      · exact (hNoCont r trivial ⟨rfl, hl S c hS r hr⟩
          ⟨ha S c hS r hr, v, hv, hFalse⟩).elim
    · exact no ⟨c, hcc, hNone⟩

/-- Exact finite evaluations for the registered three-premise core. -/
theorem noC_cont : ¬ Contingent noC false false := necessitationCore.2.1.1
theorem noC_nec : NecessaryFact noC false true := necessitationCore.2.1.2.1
theorem noC_imp : NecessaryImplication noC false true false := necessitationCore.2.1.2.2
theorem noN_cont : Contingent noN false false := necessitationCore.2.2.1.1
theorem noN_nec : ¬ NecessaryFact noN false true := necessitationCore.2.2.1.2.1
theorem noN_imp : NecessaryImplication noN false true false := necessitationCore.2.2.1.2.2
theorem noS_cont : Contingent noS false false := necessitationCore.2.2.2.1
theorem noS_nec : NecessaryFact noS false true := necessitationCore.2.2.2.2.1
theorem noS_imp : ¬ NecessaryImplication noS false true false := necessitationCore.2.2.2.2.2

private theorem falseMemberCont : Contingent falseMember false false :=
  ⟨rfl, true, trivial, Bool.noConfusion⟩
private theorem bothContingent (f : Bool) : Contingent bothCont false f := by
  cases f <;> exact ⟨rfl, true, trivial, Bool.noConfusion⟩
private theorem everySelf : EveryContingentComplete bothCont false selfG :=
  fun f _ => ⟨(fun r => r = f), rfl⟩
private theorem everyEmpty : EveryContingentComplete bothCont false emptyG :=
  fun _ _ => ⟨(fun _ => False), rfl⟩

theorem contingentTerminusMap : ContingentTerminus := by
  refine ⟨fun _ _ _ A a R G x em hc hf ha hl hn => contingentTerminus A a R G x em hc hf ha hl hn,
    ⟨?_, emptyWF, ?_, ?_, ?_, ?_⟩,
    ⟨falseMemberCont, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨bothContingent false, emptyWF, ?_, ?_, ?_, everySelf⟩,
    ⟨bothContingent false, emptyWF, ?_, ?_, ?_, everyEmpty⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · intro _ _ h; exact h.elim
  · intro _ _ h; exact h.elim
  · intro _ _ h; exact h.elim
  · exact ⟨(), ⟨rfl, true, trivial, Bool.noConfusion⟩, fun ⟨_, h⟩ => h.elim⟩
  · apply shallowWF
    intro x y z hxy hyz
    exact Bool.noConfusion (hxy.2.symm.trans hyz.1)
  · intro h
    exact h (fun r => r = true) false ⟨rfl, rfl⟩ true rfl
  · intro S f h r hr
    rcases h with ⟨hS, hf⟩
    rw [hS] at hr
    exact ⟨hr, hf⟩
  · intro S f h v _ hall
    exact (hall true (h.1 ▸ rfl)).elim
  · intro f hc
    cases f with
    | false => exact ⟨_, rfl, rfl⟩
    | true => exact hc.1.elim
  · intro S f hS r hr
    cases r <;> rfl
  · intro h
    exact h (fun r => r = false) false rfl false rfl
  · intro S f hS v _ hall
    exact hall f (hS ▸ rfl)
  · intro S f hS r hr
    exact (hS ▸ hr).elim
  · intro S f hS r hr
    exact (hS ▸ hr).elim
  · intro h
    exact Bool.noConfusion (h (fun _ => False) false rfl true trivial (fun _ h => h.elim))
  · exact ⟨rfl, true, trivial, Bool.noConfusion⟩
  · intro h
    exact h.not_rightTotal (fun n => ⟨n + 1, rfl⟩)
  · intro _ _ _ _ _; rfl
  · intro S f hS r hr
    change S = (fun r => r = f + 1) at hS
    rw [hS] at hr
    exact hr
  · intro S f hS v _ hall
    exact hall (f + 1) (hS ▸ rfl)
  · intro f _; exact ⟨(fun r => r = f + 1), rfl⟩

private theorem effectEdges : fullDependency Event.effectA Event.effectB ∧
    fullDependency Event.effectB Event.effectA :=
  ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

theorem enablingCycle : EnablingCycle := by
  have hw : WellFounded groundRule := by
    apply shallowWF
    intro x y z hxy hyz
    rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rcases hyz with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  have rules : ∀ on, SatisfiesRules on := by
    intro on f hf
    rcases hf with rfl | rfl
    · constructor
      · intro h
        exact ⟨.baseA, Or.inl ⟨rfl, rfl⟩, trivial, fun e he => by
          rcases he with ⟨rfl, _⟩ | ⟨_, he⟩
          · exact h
          · cases he⟩
      · rintro ⟨r, hr, _, hall⟩
        exact hall .effectB (Or.inl ⟨rfl, rfl⟩)
    · constructor
      · intro h
        exact ⟨.baseB, Or.inr ⟨rfl, rfl⟩, trivial, fun e he => by
          rcases he with ⟨_, he⟩ | ⟨rfl, _⟩
          · cases he
          · exact h⟩
      · rintro ⟨r, hr, _, hall⟩
        exact hall .effectA (Or.inr ⟨rfl, rfl⟩)
  have cyc : Relation.TransGen fullDependency .effectA .effectA :=
    (Relation.TransGen.single effectEdges.1).tail effectEdges.2
  refine ⟨hw, (Graph.controls_of_wellFounded ⟨groundRule⟩ hw).1,
    rules true, rules false, (fun _ => ⟨trivial, trivial⟩),
    ⟨rfl, true, trivial, Bool.noConfusion⟩, ⟨rfl, true, trivial, Bool.noConfusion⟩,
    Event.noConfusion, ?_, cyc, ?_⟩
  · apply (TruthCore.Results.Explanation.CondensationSufficiency.comp_eq_iff _ _ _).2
    exact ⟨Relation.ReflTransGen.single effectEdges.1, Relation.ReflTransGen.single effectEdges.2⟩
  · intro h
    exact (Graph.controls_of_wellFounded ⟨fullDependency⟩ h).1 _ cyc
end TruthCore.Results.Explanation.GroundingBaseline
