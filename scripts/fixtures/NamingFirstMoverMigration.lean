import TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.Solution

namespace TruthCore.NamingFirstMoverMigrationFixture
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

def act : Unit → Unit → Prop := fun _ _ => False
def more : Unit → Unit → Unit → Prop := fun _ _ _ => False
def cause : Unit → Unit → Unit → Prop := fun _ _ _ => False
def relation : Unit → Unit → Prop := fun _ _ => False
def god : Unit → Prop := fun _ => False

/-- Both complete equality-decision bridge applications hold on an inhabited
carrier with no maximum, no first mover and no God. They cannot supply existence.
These are formal controls, not claims of metaphysical possibility. -/
theorem conditionalBridgesSupplyNoExistence :
    MaximeEnsIsGod act more () god ∧
    FirstUnmovedMoverIsMaximeEns act cause act more () ∧
    ¬ (∃ m, IsMaximumIn act more () m) ∧
    ¬ ThereIsAFirstUnmovedMover act cause ∧ ¬ GodExists god := by
  have hGenus : MaximumInGenusCausesAllInGenusReading act more cause :=
    fun _ _ hm => hm.1.elim
  have hNamed :=
    TruthCore.Results.Aquinas.SummaTheologiae.MaximeEnsIsGodViaFullDescriptionIdentity.maximeEnsIsGodViaFullDescription
      act more cause () relation relation god hGenus
      (fun _ _ _ _ h => h.elim) (fun _ _ h => h.elim)
      (fun _ _ _ h => h.elim) (fun _ _ h => h.elim)
      (fun _ hm => hm.1.elim) (fun _ hm => hm.1.elim)
  have hSame :=
    TruthCore.Results.Aquinas.SummaTheologiae.FirstMoverIsMaximeEnsIdentity.firstMoverIsMaximeEns
      act cause act more cause () god hGenus (fun _ _ _ h => h.elim)
      (fun _ _ h => h.elim) hNamed (fun _ _ hg => hg.elim)
  refine ⟨hNamed, hSame, ?_, ?_, ?_⟩
  · rintro ⟨m, hm⟩; exact hm.1.elim
  · rintro ⟨f, ⟨x, r, hm⟩, _⟩; exact hm.elim
  · rintro ⟨g, hg⟩; exact hg.elim
end TruthCore.NamingFirstMoverMigrationFixture
