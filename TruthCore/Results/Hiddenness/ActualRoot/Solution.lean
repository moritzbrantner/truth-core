module
public import TruthCore.Hiddenness.ActualRoot
public import TruthCore.Results.Hiddenness.PremisesIndependent.Solution
public import TruthCore.Results.Hiddenness.NontheisticConsistent.Solution

@[expose] public section
namespace TruthCore.Results.Hiddenness.ActualRoot
open TruthCore.Hiddenness TruthCore.Hiddenness.ActualRoot

theorem loveWeakens (s : Sig) (h : GodLoves s) : ActualGodLoves s := by
  exact h s.actual

theorem openWeakens (s : Sig) (h : AlwaysOpen s) : ActualAlwaysOpen s := by
  exact h s.actual

theorem beliefWeakens (s : Sig) (h : AccessNeedsBelief s) : ActualAccessNeedsBelief s := by
  exact h s.actual

theorem noGod (s : Sig) (hLove : ActualGodLoves s) (hOpen : ActualAlwaysOpen s)
    (hBelief : ActualAccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s) : NoGod s := by
  intro hGod
  obtain ⟨p, t, hCapable, hNonresistant, hLacks⟩ := hNonbelief
  exact hBelief p t hLacks (hOpen (hLove hGod) p t hCapable hNonresistant)

theorem noRouteGod {B : Type} (IsGod : B → Prop) (s : Sig)
    (hLove : ActualGodLoves s) (hOpen : ActualAlwaysOpen s)
    (hBelief : ActualAccessNeedsBelief s) (hNonbelief : NonresistantNonbelief s)
    (hIdentification : RouteIdentification IsGod s) : NoRouteGod IsGod := by
  rintro ⟨g, hg⟩
  exact noGod s hLove hOpen hBelief hNonbelief (hIdentification g hg)

theorem controls : Controls := by
  have independent := TruthCore.Results.Hiddenness.PremisesIndependent.premisesIndependent
  obtain ⟨s1, ho1, hb1, hn1, hg1⟩ := independent.1
  obtain ⟨s2, hl2, hb2, hn2, hg2⟩ := independent.2.1
  obtain ⟨s3, hl3, ho3, hn3, hg3⟩ := independent.2.2.1
  obtain ⟨s4, hl4, ho4, hb4, hg4⟩ := independent.2.2.2
  obtain ⟨sn, hNo, hl, ho, hb, hn⟩ :=
    TruthCore.Results.Hiddenness.NontheisticConsistent.nontheisticConsistent
  refine ⟨⟨sn, loveWeakens _ hl, openWeakens _ ho, beliefWeakens _ hb, hn,
    (fun _ h => h.elim), hNo⟩, ?_, ?_, ?_,
    ⟨s1, openWeakens _ ho1, beliefWeakens _ hb1, hn1, hg1⟩,
    ⟨s2, loveWeakens _ hl2, beliefWeakens _ hb2, hn2, hg2⟩,
    ⟨s3, loveWeakens _ hl3, openWeakens _ ho3, hn3, hg3⟩,
    ⟨s4, loveWeakens _ hl4, openWeakens _ ho4, beliefWeakens _ hb4, hg4⟩,
    ⟨sn, loveWeakens _ hl, openWeakens _ ho, beliefWeakens _ hb, hn,
      ⟨(), trivial⟩, fun h => hNo (h () trivial)⟩⟩
  · refine ⟨remoteModel true false false false, ?_, ?_⟩
    · intro h; exact (Bool.false_ne_true h.1).elim
    · intro h; exact Bool.false_ne_true (h true ⟨rfl, rfl⟩).2
  · refine ⟨remoteModel false true false false, ?_, ?_⟩
    · intro h; exact (Bool.false_ne_true h.1).elim
    · intro h; exact Bool.false_ne_true (h true ⟨rfl, rfl⟩ () false trivial (fun h => h)).2
  · refine ⟨remoteModel false false true false, ?_, ?_⟩
    · intro _ _ _ h; exact Bool.false_ne_true h.1
    · intro h
      exact h true () false Bool.false_ne_true ⟨rfl, rfl⟩
end TruthCore.Results.Hiddenness.ActualRoot
