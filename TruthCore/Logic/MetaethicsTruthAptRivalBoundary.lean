module

public import TruthCore.English.VanRoojen.MoralCognitivism

/-!
Exact truth-aptness rival endpoints. The attributed source definitions are
unchanged. Their shared moral-content predicate may be empty; nonemptiness is
supplied separately by the existing Geach witness. A raw universal quasi-realist
answer is therefore not used as the logical negation of robust universal truth
aptness. This module adds no exhaustive classification of metaethical theories.
-/
@[expose] public section
namespace TruthCore.Logic.MetaethicsTruthAptRivalBoundary
open TruthCore.English.VanRoojen

/-- Exact negation of the existing robust-universal answer under the same
moral and robust-aptness predicates; minimal aptness is not silently robust. -/
def NotRealistRobustTruthApt {Sentence : Type}
    (Moral RobustlyTruthApt : Sentence → Prop) : Prop :=
  ¬ RealistRobustTruthAptReading Moral RobustlyTruthApt

/-- Prior finite witnesses exported with the properties relevant to closure:
empty moral scope admits both source answers; a nonempty scope may reject both.
Thus the two named answers are neither exclusive without a witness nor exhaustive.
These are models of the exact reading predicates, not entire historical theories. -/
def Controls : Prop :=
  (∃ (Moral Minimal Robust : Unit → Prop),
    QuasiRealistMinimalTruthAptReading Moral Minimal Robust ∧
    RealistRobustTruthAptReading Moral Robust ∧ (∀ s, ¬ Moral s)) ∧
  (∃ (Moral Minimal Robust : Unit → Prop),
    GeachMinorPremiseIsMoralReading Moral () ∧
    ¬ QuasiRealistMinimalTruthAptReading Moral Minimal Robust ∧
    NotRealistRobustTruthApt Moral Robust)

end TruthCore.Logic.MetaethicsTruthAptRivalBoundary
