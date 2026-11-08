module

public import TruthCore.Causality.RootPurity
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityEternity

/-! Unrestricted perfection from whole power of being; uniqueness from perfect
beings (SCG I.28, ST I q.4 a.2, SCG I.42; #320)

Typed homes for three source statements that entered the corpus through
definition records and had no argument consumer:
* `STMT-AQUINAS-SCG-I28-OWN-BEING-WHOLE-POWER-PERFECTION`: what is its own being
  lacks no excellence belonging to being (`OwnBeingLacksNoPerfectionOfBeing`).
  Only "lacks no excellence" is encoded; "has no defect" is not used.
* `STMT-ALL-PERFECTIONS-PERTAIN-TO-PERFECTION-OF-BEING`: every pure perfection is
  a perfection of being (`PurePerfectionsPertainToBeing`). Read for pure
  perfections only, which is weaker than "every perfection of a thing".
* `STMT-AQUINAS-SCG-I42-PERFECT-BEINGS-DIFFERENTIATION`: beings each lacking no
  perfection and having no admixture of imperfection are not several
  (`PerfectBeingsNotSeveral`).

`OwnBeing x` ("x is its own being", subsistent esse) is a primitive predicate.
The SCG I.28 claim warns that this is not a consequence of a represented
essence/esse equality, so the step from having no represented limiting principle
to being one's own being is the explicit OPEN analyst bridge
`UnlimitedIsOwnBeing`, attributed to no source. -/

@[expose] public section

namespace TruthCore.Causality.WholePowerPerfection
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)

variable {B D P : Type}

/-- SCG I.28 [2–3], encoded part: whatever is its own being has every
determination that is a perfection of being. -/
def OwnBeingLacksNoPerfectionOfBeing
    (OwnBeing : B → Prop) (Has : B → D → Prop) (OfBeing : D → Prop) : Prop :=
  ∀ x, OwnBeing x → ∀ d, OfBeing d → Has x d

/-- ST I q.4 a.2, restricted to pure perfections: each pure perfection pertains
to the perfection of being. -/
def PurePerfectionsPertainToBeing (Pure OfBeing : D → Prop) : Prop :=
  ∀ d, Pure d → OfBeing d

/-- OPEN analyst bridge: a being with none of the three represented limiting
principles is its own being. -/
def UnlimitedIsOwnBeing (Composite : B → Prop) (Prior : B → B → Prop)
    (essence esse : B → P) (OwnBeing : B → Prop) : Prop :=
  ∀ x, ¬ HasLimitingPrinciple Composite Prior essence esse x → OwnBeing x

/-- SCG I.42 [3]: two beings, each having every pure perfection and only pure
perfections among its real determinations, are one. Ranges over all beings. -/
def PerfectBeingsNotSeveral (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ x y, (∀ d, Pure d → Has x d) → (∀ d, Has x d → Pure d) →
    (∀ d, Pure d → Has y d) → (∀ d, Has y d → Pure d) → x = y

/-- OPEN analyst bridge, near-definitional under DEF-INFINITE ("infinity of
perfection"): whatever is infinite has every pure perfection. `Infinite` stays the
primitive predicate of `SubsistentBeingIsInfiniteReading` and `GodIsInfinite`. -/
def InfiniteHasEveryPurePerfection (Infinite : B → Prop) (Has : B → D → Prop)
    (Pure : D → Prop) : Prop :=
  ∀ x, Infinite x → ∀ d, Pure d → Has x d

namespace Control
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility (PurelyDeterminedIndiscerniblesIdentical)
open TruthCore.Causality.RootPurity.Control (fmMoved fmMoves none1 none2 flat)

/-- Two inert beings with no determinations; one pure determination exists. -/
def inertHas (_ : Bool) (_ : Unit) : Prop := False

/-- Finite interpretations; satisfiability of encoded bundles only.
* SCG I.42 is strictly weaker than the narrower bridge: two determination-free
  beings are purely determined and indiscernible yet distinct, while I.42 holds
  vacuously because neither has the one pure perfection.
* SCG I.42 omitted: on the unchanged part-free model, unrestricted perfection and
  strict pure actuality hold, I.42 fails, at-most-one fails.
* Whole-power bridge omitted: a simple first mover that is first in being, with
  SCG I.28 and q.4 a.2, lacks the one pure perfection when it is not its own
  being; unrestricted perfection fails.
* SCG I.28 omitted: the first mover owns its being but lacks the perfection.
* q.4 a.2 omitted: the pure perfection is not a perfection of being.
* Positive witness: all inputs of the unrestricted-perfection derivation hold
  with an actual first mover.
* Infinity bridge omitted: the simple first mover is infinite under the q.7
  reading but lacks the pure perfection; with the bridge it has it. -/
def Certificate : Prop :=
  (PerfectBeingsNotSeveral inertHas (fun _ => True) ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical inertHas (fun _ => True)) ∧
  (FirstMoverHasEveryPureDetermination TruthCore.Causality.PartFreePlurality.moved
      TruthCore.Causality.PartFreePlurality.moves Control.actHas Control.allPure ∧
    FirstMoverDeterminationsArePure TruthCore.Causality.PartFreePlurality.moved
      TruthCore.Causality.PartFreePlurality.moves Control.actHas Control.allPure ∧
    ¬ PerfectBeingsNotSeveral Control.actHas Control.allPure ∧
    ¬ TruthCore.Case.Catholicism.AtMostOneFirstUnmovedMover
      TruthCore.Causality.PartFreePlurality.moved TruthCore.Causality.PartFreePlurality.moves) ∧
  (TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverIsSimpleReading
      fmMoved fmMoves none1 none1 none1 flat.essenceOf flat.esseOf ∧
    TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing fmMoved fmMoves none2 ∧
    ¬ UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => False) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => False) inertHas (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    ¬ OwnBeingLacksNoPerfectionOfBeing (fun _ => True) inertHas (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => True) inertHas (fun _ => False) ∧
    ¬ PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => False) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True)) ∧
  (UnlimitedIsOwnBeing none1 none2 flat.essenceOf flat.esseOf (fun _ => True) ∧
    OwnBeingLacksNoPerfectionOfBeing (fun _ => True) (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True) ∧
    PurePerfectionsPertainToBeing (fun (_ : Unit) => True) (fun _ => True) ∧
    FirstMoverHasEveryPureDetermination fmMoved fmMoves (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True) ∧
    TruthCore.Case.Catholicism.IsFirstUnmovedMover fmMoved fmMoves true) ∧
  (TruthCore.Latin.Aquinas.SummaTheologiae.SubsistentBeingIsInfiniteReading
      flat.essenceOf flat.esseOf (fun _ => True) ∧
    ¬ InfiniteHasEveryPurePerfection (fun _ => True) inertHas (fun _ => True) ∧
    ¬ FirstMoverHasEveryPureDetermination fmMoved fmMoves inertHas (fun _ => True) ∧
    InfiniteHasEveryPurePerfection (fun _ => True) (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True))

end Control
end TruthCore.Causality.WholePowerPerfection
