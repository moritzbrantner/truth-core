module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.IntellectWill

/-! Will from the inclination that follows intelligible form (ST I q.19 a.1; #355)

`STMT-WILL-FOLLOWS-INTELLECT` is an underived leaf of 18 root routes. Q.19 a.1
argues for it: as a natural thing is in act through its form and has a natural
inclination following that form, an intellect is in act through an intelligible
form, and an inclination follows that form too; this inclination is will.

Typed with forms, so that the steps can fail separately:
* `HasForm x f`: `x` is in act through form `f`, natural or intelligible;
* `Intelligible f`: `f` is an intelligible (apprehended) form;
* `InclinedTo x f`: `x` has an inclination following `f`. This is orientation at
  the level of nature or power, covering seeking an absent good and resting in a
  possessed one. It asserts no current exercise and no passivity
  (`DISAMB-APPETITE-POWER-AND-EXERCISE`, `DISAMB-CREATURE-PASSIVE-APPETITE-AND-DIVINE-WILL`).

Natural inclination following a natural form is not will
(`DISAMB-NATURAL-AND-COGNITIVE-APPETITE`); the controls include an intellect-less
case where a natural form has its inclination and no will follows. The primitive
`HasWill` is unchanged; the recognition step is an explicit premise. Analyst
formulation of the q.19 a.1 argument; attribution of the steps deferred. -/

@[expose] public section

namespace TruthCore.Causality.IntellectualInclination

variable {B F : Type}

/-- q.19 a.1, analogy premise: some inclination follows every form a thing has. -/
def EveryFormHasInclination (HasForm InclinedTo : B → F → Prop) : Prop :=
  ∀ x f, HasForm x f → InclinedTo x f

/-- q.19 a.1 with q.14 a.1: whatever has intellect is in act through some
intelligible form. -/
def IntellectHasIntelligibleForm (HasIntellect : B → Prop) (HasForm : B → F → Prop)
    (Intelligible : F → Prop) : Prop :=
  ∀ x, HasIntellect x → ∃ f, Intelligible f ∧ HasForm x f

/-- Recognition step, near-definitional under `DEF-HAS-WILL`: a thing with an
inclination following an intelligible form has will. -/
def IntelligibleInclinationIsWill (Intelligible : F → Prop)
    (InclinedTo : B → F → Prop) (HasWill : B → Prop) : Prop :=
  ∀ x f, Intelligible f → InclinedTo x f → HasWill x

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae (WillFollowsIntellectReading)

/-- Form `true` is intelligible, `false` natural. -/
def intelligible (f : Bool) : Prop := f = true
def intelligibleForm (_ : Unit) (f : Bool) : Prop := f = true
def naturalForm (_ : Unit) (f : Bool) : Prop := f = false
def noInclination (_ : Unit) (_ : Bool) : Prop := False
def intellect (_ : Unit) : Prop := True

/-- Finite interpretations with one intellectual being. Each premise is omitted
in turn with the other two holding, and will fails; all three hold with will.
The second case is a being whose only form is natural: its inclination follows,
but no will. -/
def Certificate : Prop :=
  (¬ EveryFormHasInclination intelligibleForm noInclination ∧
    IntellectHasIntelligibleForm intellect intelligibleForm intelligible ∧
    IntelligibleInclinationIsWill intelligible noInclination (fun _ => False) ∧
    ¬ WillFollowsIntellectReading intellect (fun _ => False)) ∧
  (EveryFormHasInclination naturalForm naturalForm ∧
    ¬ IntellectHasIntelligibleForm intellect naturalForm intelligible ∧
    IntelligibleInclinationIsWill intelligible naturalForm (fun _ => False) ∧
    ¬ WillFollowsIntellectReading intellect (fun _ => False)) ∧
  (EveryFormHasInclination intelligibleForm intelligibleForm ∧
    IntellectHasIntelligibleForm intellect intelligibleForm intelligible ∧
    ¬ IntelligibleInclinationIsWill intelligible intelligibleForm (fun _ => False) ∧
    ¬ WillFollowsIntellectReading intellect (fun _ => False)) ∧
  (EveryFormHasInclination intelligibleForm intelligibleForm ∧
    IntellectHasIntelligibleForm intellect intelligibleForm intelligible ∧
    IntelligibleInclinationIsWill intelligible intelligibleForm (fun _ => True) ∧
    WillFollowsIntellectReading intellect (fun _ => True))

end Control
end TruthCore.Causality.IntellectualInclination
