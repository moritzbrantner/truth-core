import TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributes.Solution

/-! Regression settings, not metaphysical interpretations or corpus closure.
The positive setting retains the original explicit excluded-middle premise. -/
namespace TruthCore.ClassicalAttributesMigrationFixture
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

def base : Signature where
  Being := Unit
  IsGod := fun _ => True
  HasClassicalAttributes := fun _ => True
  RevealsRecognizably := fun _ => True
  jesus := ()
  ClaimedDivineAuthority := fun _ => True
  RoseFromTheDead := fun _ => True
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => True
  VisibleWithAuthority := fun _ => True
  FoundedAsTeachingAuthority := fun _ _ => True
  DefinitivelyProposesAsRevealed := fun _ _ => True
  creedOneGodFatherAlmightyCreator := True
  creedOneLordJesusChristOnlyBegottenConsubstantial := True
  creedIncarnateOfSpiritAndVirginMary := True
  creedCrucifiedUnderPilateSufferedBuried := True
  creedRoseOnTheThirdDay := True
  creedAscendedSeatedAtRightHand := True
  creedWillComeToJudgeKingdomWithoutEnd := True
  creedHolySpiritLordGiverOfLife := True
  creedOneHolyCatholicApostolicChurch := True
  creedOneBaptismForForgiveness := True
  creedResurrectionOfTheDead := True
  creedLifeOfTheWorldToCome := True

def act : Unit → Unit → Prop := fun _ _ => True
def more : Unit → Unit → Unit → Prop := fun _ _ _ => False
def cause : Unit → Unit → Unit → Prop := fun _ _ _ => False
def yes : Unit → Prop := fun _ => True
def no : Unit → Prop := fun _ => False

/-- All nonlogical premises can hold together with an actual IsGod witness.
This does not prove the retained logical floor premise from nothing. -/
theorem inhabitedSetting (hEM : TruthCore.Logic.ExcludedMiddle) :
    GodHasClassicalAttributes base ∧ (∃ g, base.IsGod g) := by
  have hGenus : MaximumInGenusCausesAllInGenusReading act more cause := by
    intro r m _ x hOther _
    exact (hOther (Subsingleton.elim x m)).elim
  have hMax : GodIsMaximalInBeing base.IsGod act more () :=
    fun _ _ => ⟨True.intro, fun _ h => h⟩
  have hResult :=
    TruthCore.Results.Case.Catholicism.StageTwo.ClassicalAttributes.godHasClassicalAttributes
      base act act more cause () no yes yes yes yes yes
      (fun _ _ _ _ _ _ _ _ _ _ => True.intro) hMax hGenus
      (fun _ _ _ _ h => h.elim) hEM (fun _ h => h.elim)
      (fun _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro)
      (fun _ _ => Iff.rfl) (fun _ _ _ h => h.elim)
      (fun _ _ => True.intro) (fun _ _ => True.intro)
      (fun _ _ => True.intro) (fun _ _ => True.intro) (fun _ _ => True.intro)
  exact ⟨hResult, ⟨(), True.intro⟩⟩

/-- An inhabited Being carrier does not make IsGod inhabited. -/
theorem emptyGodSetting :
    let σ := { base with IsGod := no, HasClassicalAttributes := no }
    GodHasClassicalAttributes σ ∧ ¬ (∃ g, σ.IsGod g) := by
  exact ⟨fun _ h => h.elim, fun ⟨_, h⟩ => h⟩

/-- Even the sufficiency premise plus the field cannot recover the nine
attributes. This is a concrete counterexample to the unadvertised converse. -/
theorem noConverse :
    ClassicalAttributesSuffice base no no no no no no no no no ∧
    base.HasClassicalAttributes () ∧
    ¬ NineClassicalAttributes no no no no no no no no no () := by
  exact ⟨fun _ h => h.elim, True.intro, fun h => h.1⟩

/-- The compatibility predicate has exactly its old body for arbitrary inputs. -/
example {Being Respect : Sort _} (p : Being → Respect → Prop) (g : Being) :
    IsImmutable p g ↔ ∀ r, ¬ p g r := isImmutable_iff_noPotency p g

end TruthCore.ClassicalAttributesMigrationFixture
