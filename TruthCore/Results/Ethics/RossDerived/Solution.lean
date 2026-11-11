module
public import TruthCore.Ethics.RossDerived
@[expose] public section
namespace TruthCore.Results.Ethics.RossDerived
open TruthCore.Ethics.RossPermission TruthCore.Ethics.RossDerived

theorem mailCharacterization (q : Action → Prop) : Derived issuedMail q ↔ q .mail := by
  constructor
  · rintro ⟨p, hp, hq⟩
    exact hq .mail ((hp .mail).mpr rfl)
  · intro h
    exact ⟨mail, fun _ => Iff.rfl, fun a ha => by cases ha; exact h⟩

theorem pairSatisfiable (p : Action → Prop) (hp : issuedPair.issued p) : ∃ a, p a := by
  rcases hp with hm | hb
  · exact ⟨.mail, (hm .mail).mpr rfl⟩
  · exact ⟨.burn, (hb .burn).mpr rfl⟩

theorem certificate : TruthCore.Ethics.RossDerived.Certificate := by
  refine ⟨?_, ?_, ?_, mailCharacterization, ?_, ?_, ?_, ?_⟩
  · intro W n p hp
    exact ⟨p, hp, fun _ h => h⟩
  · intro W n p q he
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, fun a ha => (he a).mp (h a ha)⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, fun a ha => (he a).mpr (h a ha)⟩
  · rintro W n p q ⟨r, hr, h⟩ he
    exact ⟨r, hr, fun a ha => he a (h a ha)⟩
  · rintro q ⟨p, hp, _⟩
    exact hp
  · intro q
    exact ⟨fun _ => False, fun _ => Iff.rfl, fun _ h => False.elim h⟩
  · constructor
    · exact (mailCharacterization _).mpr (Or.inl rfl)
    · intro h
      have hh := (mailCharacterization _).mp h
      cases hh
  · refine ⟨pairSatisfiable, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      have hm := ha mail (Or.inl (fun _ => Iff.rfl))
      have hb := ha burn (Or.inr (fun _ => Iff.rfl))
      cases hm
      cases hb
    · exact ⟨mail, Or.inl (fun _ => Iff.rfl), fun _ h => h⟩
    · exact ⟨burn, Or.inr (fun _ => Iff.rfl), fun _ h => h⟩
    · rintro ⟨p, hp, h⟩
      obtain ⟨a, ha⟩ := pairSatisfiable p hp
      obtain ⟨hm, hb⟩ := h a ha
      cases hm
      cases hb
    · rintro ⟨p, hp, h⟩
      obtain ⟨a, ha⟩ := pairSatisfiable p hp
      exact h a ha
end TruthCore.Results.Ethics.RossDerived
