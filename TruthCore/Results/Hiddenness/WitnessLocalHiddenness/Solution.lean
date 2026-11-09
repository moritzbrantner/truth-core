module
public import TruthCore.Hiddenness.WitnessLocalHiddenness
public import TruthCore.Results.Hiddenness.ActualRoot.Solution
@[expose] public section
namespace TruthCore.Results.Hiddenness.WitnessLocalHiddenness
open TruthCore.Hiddenness TruthCore.Hiddenness.ActualRoot
open TruthCore.Hiddenness.WitnessLocalHiddenness

theorem openWeakens (s : Sig) (h : ActualAlwaysOpen s) : WitnessOpen s := by
  intro p t hg hl
  exact h hl p t hg.1 hg.2.1

theorem accessWeakens (s : Sig) (h : ActualAccessNeedsBelief s) : WitnessAccess s := by
  intro p t hg
  exact h p t hg.2.2

theorem selectWitness (s : Sig) (ho : WitnessOpen s) (ha : WitnessAccess s)
    (hn : NonresistantNonbelief s) : SelectedBundle s := by
  obtain ⟨p,t,hg⟩ := hn
  exact ⟨p,t,hg,ho p t hg,ha p t hg⟩

theorem noGod (s : Sig) (hl : ActualGodLoves s) (hs : SelectedBundle s) : NoGod s := by
  intro hg
  obtain ⟨p,t,_,ho,ha⟩ := hs
  exact ha (ho (hl hg))

theorem noRouteGod {B : Type} (IsGod : B → Prop) (s : Sig)
    (hl : ActualGodLoves s) (hs : SelectedBundle s)
    (hi : RouteIdentification IsGod s) : NoRouteGod IsGod := by
  rintro ⟨g,hg⟩
  exact noGod s hl hs (hi g hg)

theorem guardEquivalent (s : Sig) (hn : NonresistantNonbelief s) :
    (GuardedLove s ↔ ActualGodLoves s) := by
  exact ⟨fun h => h hn, fun h _ => h⟩

theorem controls : TruthCore.Hiddenness.WitnessLocalHiddenness.Controls := by
  have old := TruthCore.Results.Hiddenness.ActualRoot.controls
  obtain ⟨sn,hl,ho,ha,hn,_,hno⟩ := old.1
  obtain ⟨s1,ho1,ha1,hn1,hg1⟩ := old.2.2.2.2.1
  obtain ⟨s2,hl2,ha2,hn2,hg2⟩ := old.2.2.2.2.2.1
  obtain ⟨s3,hl3,ho3,hn3,hg3⟩ := old.2.2.2.2.2.2.1
  obtain ⟨s4,hl4,ho4,ha4,hg4⟩ := old.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ⟨sn,hl,selectWitness _ (openWeakens _ ho) (accessWeakens _ ha) hn,hno⟩,
    ⟨s1,openWeakens _ ho1,accessWeakens _ ha1,hn1,hg1⟩,
    ⟨s2,hl2,accessWeakens _ ha2,hn2,hg2⟩,
    ⟨s3,hl3,openWeakens _ ho3,hn3,hg3⟩,
    ⟨s4,hl4,openWeakens _ ho4,accessWeakens _ ha4,hg4⟩, ?_⟩
  · refine ⟨scopeModel false, ?_, ?_, ?_⟩
    · intro p t hg _
      cases t with
      | false => rfl
      | true => exact (hg.2.2 rfl).elim
    · exact ⟨(),false,trivial,(fun h => h),Bool.false_ne_true⟩
    · intro h
      exact Bool.false_ne_true (h rfl () true trivial (fun h => h)).symm
  · refine ⟨scopeModel true, ?_, ?_, ?_⟩
    · intro p t hg ha
      exact Bool.false_ne_true (hg.1.symm.trans ha)
    · exact ⟨(),false,rfl,(fun h => h),(fun h => h)⟩
    · intro h
      exact h () true (fun h => h) rfl
  · refine ⟨delayedModel, (fun _ _ => rfl), ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · intro _ _ _ t _ _ hn
      cases t with
      | false => exact (hn rfl).elim
      | true => exact Or.inl rfl
    · intro _ _ _ hn ha
      exact hn ha
    · intro _ _ _ t _ _ ha
      cases t with
      | false => rfl
      | true => exact (ha (Or.inl rfl)).elim
    · exact ⟨(),false,trivial,(fun h => h),fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩
    · intro h
      exact (h () false ⟨trivial,(fun h => h),fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩ rfl).elim Bool.false_ne_true Bool.false_ne_true
    · exact ⟨(),false,⟨trivial,(fun h => h),fun h => h.elim Bool.false_ne_true Bool.false_ne_true⟩,rfl,(fun h => h)⟩
end TruthCore.Results.Hiddenness.WitnessLocalHiddenness
