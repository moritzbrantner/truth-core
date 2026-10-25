import TruthCore.Modal.DResearch.Scopes
import TruthCore.Results.Modal.DResearch.Witnesses.Solution
namespace TruthCore.Results.Modal.DResearch.Scopes
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite (Model deadEnd)
open TruthCore.Modal.DResearch
open TruthCore.Isabelle.AFP.GoedelGod (Dia Box)
open TruthCore.Results.Modal.DResearch.Witnesses (pocketOne forkOne forkTwo)

private theorem pocketTwoSuccessor (v : PocketWorld) :
    pocket.frame.access 2 v ↔ v = 3 := by
  have h : ∀ v : PocketWorld, pocket.frame.access 2 v ↔ v = 3 := by
    intro v; cases v
    all_goals constructor <;> intro h
    all_goals first | rfl | exact Bool.noConfusion h | exact PocketWorld.noConfusion h
  exact h v
private theorem pocketThreeSuccessor (v : PocketWorld) :
    pocket.frame.access 3 v ↔ v = 2 := by
  have h : ∀ v : PocketWorld, pocket.frame.access 3 v ↔ v = 2 := by
    intro v; cases v
    all_goals constructor <;> intro h
    all_goals first | rfl | exact Bool.noConfusion h | exact PocketWorld.noConfusion h
  exact h v

private theorem pocketUniform (p : Formula Unit) :
    Holds pocket.frame pocket.valuation 2 p ↔ Holds pocket.frame pocket.valuation 3 p := by
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
      have he := (pocketThreeSuccessor v).mp hv
      subst v
      exact hp.mpr (h 3 rfl)
    · intro h v hv
      have he := (pocketTwoSuccessor v).mp hv
      subst v
      exact hp.mp (h 2 rfl)
  | diamond p hp =>
    constructor
    · rintro ⟨v, hv, ht⟩
      have he := (pocketTwoSuccessor v).mp hv
      subst v
      exact ⟨2, rfl, hp.mpr ht⟩
    · rintro ⟨v, hv, ht⟩
      have he := (pocketThreeSuccessor v).mp hv
      subst v
      exact ⟨3, rfl, hp.mp ht⟩

private theorem pocketTwoLanguage :
    MC pocket.frame (expressible pocket.frame pocket.valuation) 2 := by
  rintro P ⟨p, rfl⟩ hp v hv
  have he := (pocketTwoSuccessor v).mp hv
  subst v
  exact (pocketUniform p).mp hp

private theorem restrictFull {W : Type} (F : Frame W) (D : Domain W) w
    (h : MC F allPredicates w) : MC F D w :=
  restrict F allPredicates D w (fun _ _ => trivial) h

private theorem pocketRootLanguage :
    ¬ MC pocket.frame (expressible pocket.frame pocket.valuation) 0 := by
  intro h
  have hn := h (fun w => Holds pocket.frame pocket.valuation w (.imp (.atom ()) .falsum))
    ⟨.imp (.atom ()) .falsum, rfl⟩ (fun hp => Bool.noConfusion hp) 1 rfl
  exact hn rfl
private theorem forkRootLanguage :
    ¬ MC fork.frame (expressible fork.frame fork.valuation) 0 := by
  intro h
  have hn := h (fun w => Holds fork.frame fork.valuation w (.imp (.atom ()) .falsum))
    ⟨.imp (.atom ()) .falsum, rfl⟩ (fun hp => Bool.noConfusion hp) 1 rfl
  exact hn rfl

theorem checks : ScopeChecks := by
  have hp1 := restrictFull pocket.frame (expressible pocket.frame pocket.valuation) 1 pocketOne
  have hf1 := restrictFull fork.frame (expressible fork.frame fork.valuation) 1 forkOne
  have hf2 := restrictFull fork.frame (expressible fork.frame fork.valuation) 2 forkTwo
  refine ⟨⟨?_, ?_, ?_⟩,
    ⟨pocketRootLanguage, hp1, pocketTwoLanguage, ⟨1, rfl, hp1⟩, ?_⟩,
    ⟨forkRootLanguage, hf1, hf2, ⟨1, rfl, hf1⟩, ?_⟩⟩
  · intro hSerial
    obtain ⟨v, hv⟩ := hSerial ()
    exact Bool.noConfusion (show (false : Bool) = true from hv)
  · intro P _ _ v hv
    exact Bool.noConfusion (show (false : Bool) = true from hv)
  · exact Bool.noConfusion
  · intro v hv
    have h : ∀ v : PocketWorld, pocket.frame.access 0 v → v = 1 ∨ v = 2 := by
      intro v; cases v <;> intro hv
      all_goals first | exact .inl rfl | exact .inr rfl | exact Bool.noConfusion hv
    cases h v hv with
    | inl he => exact he ▸ hp1
    | inr he => exact he ▸ pocketTwoLanguage
  · intro v hv
    have h : ∀ v : ForkWorld, fork.frame.access 0 v → v = 1 ∨ v = 2 := by
      intro v; cases v <;> intro hv
      all_goals first | exact .inl rfl | exact .inr rfl | exact Bool.noConfusion hv
    cases h v hv with
    | inl he => exact he ▸ hf1
    | inr he => exact he ▸ hf2
end TruthCore.Results.Modal.DResearch.Scopes
