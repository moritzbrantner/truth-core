import TruthCore.Modal.DResearch.Language
namespace TruthCore.Results.Modal.DResearch.Language
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.DResearch

private theorem uniform (p : Formula Unit) :
    Holds cycle.frame cycle.valuation false p ↔
    Holds cycle.frame cycle.valuation true p := by
  induction p with
  | atom a => rfl
  | falsum => rfl
  | imp p q hp hq =>
    constructor
    · intro h ht; exact hq.mp (h (hp.mpr ht))
    · intro h hf; exact hq.mpr (h (hp.mp hf))
  | box p hp =>
    constructor
    · intro h v hv
      have ht := h true rfl
      cases v with
      | false => exact hp.mpr ht
      | true => exact Bool.noConfusion (show (false : Bool) = true from hv)
    · intro h v hv
      have hf := h false rfl
      cases v with
      | false => exact Bool.noConfusion (show (false : Bool) = true from hv)
      | true => exact hp.mp hf
  | diamond p hp =>
    constructor
    · rintro ⟨v, hv, ht⟩
      cases v with
      | false => exact Bool.noConfusion (show (false : Bool) = true from hv)
      | true => exact ⟨false, rfl, hp.mpr ht⟩
    · rintro ⟨v, hv, ht⟩
      cases v with
      | false => exact ⟨true, rfl, hp.mp ht⟩
      | true => exact Bool.noConfusion (show (false : Bool) = true from hv)

private theorem languageMC (w : Bool) : MC cycle.frame cycleLanguage w := by
  rintro P ⟨p, rfl⟩ hp v _
  cases w <;> cases v
  · exact hp
  · exact (uniform p).mp hp
  · exact (uniform p).mpr hp
  · exact hp

private theorem notFull (w : Bool) : ¬ MC cycle.frame allPredicates w := by
  intro h
  have he := identity_separates cycle.frame allPredicates w trivial h (!w) (by
    cases w <;> rfl)
  cases w <;> exact Bool.noConfusion he

private theorem notIdentity : ¬ IdentityAdmissible cycleLanguage false := by
  rintro ⟨p, he⟩
  have hf : Holds cycle.frame cycle.valuation false p := (congrFun he false).mp rfl
  have ht : (true : Bool) = false := (congrFun he true).mpr ((uniform p).mp hf)
  exact Bool.noConfusion ht

theorem checks : LanguageChecks := by
  refine ⟨(by intro w; cases w; exact ⟨true, rfl⟩; exact ⟨false, rfl⟩),
    (by intro w; cases w <;> exact Bool.noConfusion), languageMC, ⟨true, rfl, languageMC true⟩,
    (fun v _ => languageMC v), notFull, notIdentity, ?_, ?_, uniform, ?_,
    ⟨⟨true, rfl, rfl⟩, Bool.noConfusion⟩, rfl, rfl, rfl⟩
  · intro hExt
    have hEq := hExt false true (by
      rintro P ⟨p, rfl⟩
      exact uniform p)
    exact Bool.noConfusion hEq
  · rintro P ⟨p, rfl⟩
    exact ⟨.imp p .falsum, rfl⟩
  · intro p ⟨⟨v, hv, ht⟩, ⟨z, hz, hn⟩⟩
    have hvEq : v = true := by
      cases v with
      | false => exact Bool.noConfusion (show (false : Bool) = true from hv)
      | true => rfl
    have hzEq : z = true := by
      cases z with
      | false => exact Bool.noConfusion (show (false : Bool) = true from hz)
      | true => rfl
    exact hn (hzEq.symm ▸ (hvEq ▸ ht))
end TruthCore.Results.Modal.DResearch.Language
