import TruthCore.Causality.RootMultiplication
namespace TruthCore.Results.Causality.RootMultiplication
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.ConstitutiveNatureUniqueness
open TruthCore.Causality.RootMultiplication

/-- With individuation, the adapter and every-perfection: distinct first movers
have one act profile and different natures, and at-most-one is equivalent to
each nature condition. The equivalences say that, given these three, either
nature condition is not independent of uniqueness. -/
theorem residue {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) (InAct : B → R → Prop)
    (suppositum essence : B → P)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hPerfect : FirstUnmovedMoverHasEveryPerfection Moved Moves InAct) :
    PluralityResidue Moved Moves InAct essence := by
  sorry

/-- The bridge's proof does not use every-perfection: simplicity and first-being
make first movers unlimited, the bridge gives common nature, and the imported Q11
theorem gives identity. Conditional on the OPEN bridge. -/
theorem uniqueFromUnlimitedNature {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body MatterForm Composite : B → Prop) (Prior : B → B → Prop)
    (suppositum essence esse : B → P)
    (hIndividual : IndividuatingBasisIsIncommunicableReading suppositum)
    (hNature : FirstMoverSuppositumIsNature Moved Moves suppositum essence)
    (hSimple : FirstUnmovedMoverIsSimpleReading Moved Moves Body MatterForm Composite essence esse)
    (hFirst : FirstUnmovedMoverIsFirstBeing Moved Moves Prior)
    (hBridge : UnlimitedBeingsShareNature Composite Prior essence esse) :
    AtMostOneFirstUnmovedMover Moved Moves := by
  sorry

theorem controls : TruthCore.Causality.RootMultiplication.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.RootMultiplication
