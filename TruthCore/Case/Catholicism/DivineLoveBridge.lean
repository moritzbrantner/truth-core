module

public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1

/-!
Analyst reconstruction of ST I q.20 a.2, tied to the existing stage-2
`GodIsSupremelyGood` and `GodHasWill`, but not inferred from either predicate's
name. Aquinas invokes q.19 a.4: the divine will, not merely an efficient cause
considered abstractly, causes the existence and goodness of things.

`CausesIn` is still the existing effective causal-responsibility parameter;
`WillsGoodFor` is a new primitive for willing some good to a recipient, and
`Loves` is a new primitive for non-passional love. Their connection, the
application of causation to willing, and the divine self-case are separately
advertised OPEN bridges. See docs/notes/divine-love-goodness-bridge.md.
-/

@[expose] public section

namespace TruthCore.Case.Catholicism.DivineLoveBridge

open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae (GoodnessIsActualityReading)

universe u v

/-- OPEN q.19 a.4 / q.20 a.2 bridge. For a distinct actual effect whose
existence God causes, having will makes that causal gift a willing of its
existence *for that recipient*. Mere `HasWill`, `CausesIn`, or the supremely-good
predicate does not contain this intentional relation. -/
def CausalExistenceWilling {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill : Being → Prop)
    (InAct : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g x, IsGod g → HasWill g → x ≠ g → InAct x esse →
    CausesIn g x esse → WillsGoodFor g x esse

/-- OPEN self-case. q.19 a.1 says God possesses and wills His own goodness;
q.20 a.1 distinguishes non-passional love from sensory passion. The inherited
unary `HasWill` records neither a particular object nor its possession. -/
def DivineOwnGoodWilling {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill : Being → Prop) (GoodIn : Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g, IsGod g → HasWill g → GoodIn g esse → WillsGoodFor g g esse

/-- OPEN interpretive bridge for q.20 a.2's `velle bonum alicui` account.
The desired good must be a good of the recipient; a bare wish that some good
exist, or mere instrumental use without any good willed to the recipient, is
not enough. For irrational creatures this need not be benevolence properly
speaking (q.20 a.2 ad 3). The rule proves no friendship, emotional passion
or equality of divine love. -/
def WillingGoodEntailsLove {Being : Sort u} {Respect : Sort v}
    (GoodIn : Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop)
    (Loves : Being → Being → Prop) : Prop :=
  ∀ g x r, GoodIn x r → WillsGoodFor g x r → Loves g x

/-- For every God `g` and every `x` in act in `esse`, there is some respect
`r` in which `x` is good (`GoodIn x r`) and such that `g` wills good to `x` in
`r`. The respect is existential here; the theorem below supplies `esse`, and
nothing is asserted about every possible good. This does not say that an act
of willing, as distinct from generic `CausesIn`, is the efficient cause of
`x`. -/
def DivineWillsGoodForAllExisting {Being : Sort u} {Respect : Sort v}
    (IsGod : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g, IsGod g → ∀ x, InAct x esse →
    ∃ r, GoodIn x r ∧ WillsGoodFor g x r

/-- Divine love of all *existing* things. The quantifier includes God Himself
if God exists, but asserts nothing about nonexistent possibles or the mode or
degree of love. It does not assert that a God exists. -/
def GodLovesAllExisting {Being : Sort u} {Respect : Sort v}
    (IsGod : Being → Prop) (InAct : Being → Respect → Prop)
    (Loves : Being → Being → Prop) (esse : Respect) : Prop :=
  ∀ g, IsGod g → ∀ x, InAct x esse → Loves g x

/-- The causal stage-2 goodness result reaches intentional good-willing only
through the two separate OPEN volitional bridges and the q.5 coextension.
The proof splits classically on `x = g` (self-case versus distinct effect), so
it depends on `Classical.choice`, `propext` and `Quot.sound` although this
module imports no Mathlib. Registering it as a zero-axiom result would need an
explicit decidability-of-identity input or a reformulated bridge. -/
theorem divineWillsGoodForAllExisting {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn WillsGoodFor esse) :
    DivineWillsGoodForAllExisting IsGod InAct GoodIn WillsGoodFor esse := by
  classical
  intro g hg x hx
  have hG := hGood g hg
  have hW := hWill g hg
  refine ⟨esse, (hActualGood x esse).2 hx, ?_⟩
  by_cases hSame : x = g
  · subst x
    exact hOwn g hg hW hG.1
  · exact hCausesWill g x hg hW hSame hx (hG.2 x esse hSame hx)

/-- q.20 a.2's final step uses its own will-good-for-another love reading, not a
derivation from a capacity for willing. -/
theorem godLovesAllExisting {Being : Sort u} {Respect : Sort v}
    (IsGod HasWill : Being → Prop)
    (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop)
    (Loves : Being → Being → Prop) (esse : Respect)
    (hGood : GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse)
    (hWill : GodHasWill IsGod HasWill)
    (hActualGood : GoodnessIsActualityReading GoodIn InAct)
    (hCausesWill : CausalExistenceWilling IsGod HasWill InAct CausesIn WillsGoodFor esse)
    (hOwn : DivineOwnGoodWilling IsGod HasWill GoodIn WillsGoodFor esse)
    (hLoveMeaning : WillingGoodEntailsLove GoodIn WillsGoodFor Loves) :
    GodLovesAllExisting IsGod InAct Loves esse := by
  intro g hg x hx
  obtain ⟨r, hgr, hwr⟩ := divineWillsGoodForAllExisting
    IsGod HasWill InAct GoodIn CausesIn WillsGoodFor esse
    hGood hWill hActualGood hCausesWill hOwn g hg x hx
  exact hLoveMeaning g x r hgr hwr

/-! A two-being structural surrogate with an actual God and an actual other;
all goodness, causation and possession predicates below are nonempty. Its
profiles vary only intentional willing and love. No modal, theological or
causal applicability claim follows from the finite assignments. -/

inductive LoveProfile where
  | complete | omitCausalWill | omitOwnWill | omitLoveMeaning
  deriving DecidableEq

def sampleIsGod (b : Bool) : Prop := b = false
def sampleHasWill (b : Bool) : Prop := b = false
def sampleInAct (_ : Bool) (_ : Unit) : Prop := True
def sampleGoodIn (_ : Bool) (_ : Unit) : Prop := True
def sampleCausesIn (g x : Bool) (_ : Unit) : Prop := g = false ∧ x = true

def sampleWillsGoodFor (p : LoveProfile) (g x : Bool) (_ : Unit) : Prop :=
  g = false ∧ match p with
    | .complete => True
    | .omitCausalWill => x = false
    | .omitOwnWill => x = true
    | .omitLoveMeaning => True

def sampleLoves (p : LoveProfile) (g x : Bool) : Prop :=
  match p with
  | .omitLoveMeaning => False
  | _ => sampleWillsGoodFor p g x ()

/-- The `Unit` respect quantifier is decided directly, without a noncomputable
choice or a general classical axiom. Bool quantifiers are already decidable. -/
private instance sampleUnitForallDecidable (P : Unit → Prop)
    [h : Decidable (P ())] : Decidable (∀ x, P x) :=
  match h with
  | isTrue hp => isTrue (fun | () => hp)
  | isFalse hn => isFalse (fun hall => hn (hall ()))

/-- The profile-indexed sample relations are decided by cases on the profile. -/
private instance sampleWillsGoodForDecidable (p : LoveProfile) (g x : Bool)
    (u : Unit) : Decidable (sampleWillsGoodFor p g x u) := by
  unfold sampleWillsGoodFor; cases p <;> infer_instance

private instance sampleLovesDecidable (p : LoveProfile) (g x : Bool) :
    Decidable (sampleLoves p g x) := by
  unfold sampleLoves; cases p <;> infer_instance

/-- Three distinct omissions keep *the exact* supreme-goodness and has-will
inputs true, and keep the other two bridges, while universal love fails.
The complete profile demonstrates nonvacuity relative to these Boolean
dictionaries. All omitted-bridge countermodels have an actual distinct effect. -/
def LoveControls : Prop :=
  let common (_p : LoveProfile) :=
    GodIsSupremelyGood sampleIsGod sampleInAct sampleGoodIn sampleCausesIn () ∧
    GodHasWill sampleIsGod sampleHasWill ∧
    GoodnessIsActualityReading sampleGoodIn sampleInAct
  let causal (p : LoveProfile) :=
    CausalExistenceWilling sampleIsGod sampleHasWill sampleInAct
      sampleCausesIn (sampleWillsGoodFor p) ()
  let own (p : LoveProfile) :=
    DivineOwnGoodWilling sampleIsGod sampleHasWill sampleGoodIn
      (sampleWillsGoodFor p) ()
  let loveMeaning (p : LoveProfile) :=
    WillingGoodEntailsLove sampleGoodIn (sampleWillsGoodFor p) (sampleLoves p)
  let loves (p : LoveProfile) :=
    GodLovesAllExisting sampleIsGod sampleInAct (sampleLoves p) ()
  sampleIsGod false ∧ sampleInAct false () ∧ sampleInAct true () ∧
    true ≠ false ∧
  common .complete ∧ causal .complete ∧ own .complete ∧
    loveMeaning .complete ∧ loves .complete ∧
  common .omitCausalWill ∧ ¬ causal .omitCausalWill ∧
    own .omitCausalWill ∧ loveMeaning .omitCausalWill ∧
    ¬ loves .omitCausalWill ∧
  common .omitOwnWill ∧ causal .omitOwnWill ∧
    ¬ own .omitOwnWill ∧ loveMeaning .omitOwnWill ∧
    ¬ loves .omitOwnWill ∧
  common .omitLoveMeaning ∧ causal .omitLoveMeaning ∧
    own .omitLoveMeaning ∧ ¬ loveMeaning .omitLoveMeaning ∧
    ¬ loves .omitLoveMeaning

theorem loveControls : LoveControls := by
  unfold LoveControls
  dsimp only
  unfold GodIsSupremelyGood IsSupremelyGood
    CausesEveryPerfectionOfOthers GodHasWill GoodnessIsActualityReading
    CausalExistenceWilling DivineOwnGoodWilling WillingGoodEntailsLove
    GodLovesAllExisting sampleIsGod sampleHasWill sampleInAct sampleGoodIn
    sampleCausesIn
  and_intros <;> decide

end TruthCore.Case.Catholicism.DivineLoveBridge
