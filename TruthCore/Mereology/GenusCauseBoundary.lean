import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article5

/-!
An analyst's joint finite control for #319/#325. The existing strict-genus
predication laws do not encode the further real-composition claims of ST I
q.3 a.5's first and third proofs. Those proofs were read in the materialized
`AQUINAS-ST-I-Q3-A5` witness; they are not refuted by these models.

The finite taxonomy classifies actual bearers and has a genus, species and
differentia. It is kept fixed while the existing q.3 a.4 efficient-cause
profile varies. No new generic composition, essence or causation vocabulary
is introduced: the relations are the existing source interfaces. These are
formal interpretations, not claims of metaphysical possibility.
-/
namespace TruthCore.Mereology.GenusCauseBoundary

open TruthCore.Greek.Aristotle.Metaphysics
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Four predicables, not four components or four additional actual beings. -/
inductive Term where
  | genus | species | differentia | being
  deriving DecidableEq

def isGenus (g : Term) : Prop := g = .genus
def differentiaOf (d g : Term) : Prop := d = .differentia ∧ g = .genus
def saidOf (t s : Term) : Prop :=
  t = .being ∨ (t = .genus ∧ s = .species) ∨
    (t = .differentia ∧ s = .species)
def inGenus (_ : Bool) (g : Term) : Prop := g = .genus
def speciesOf (_ : Bool) : Term := .species

/-- The old strict-genus clauses and a nonempty classified-bearer interface.
Genus and differentia are essentially predicated of the represented species;
neither a material component nor a causal edge is thereby stipulated. -/
def Taxonomy : Prop :=
  EveryGenusHasADifferentiaReading isGenus differentiaOf ∧
  DifferentiaeAreBeingsReading isGenus differentiaOf saidOf .being ∧
  GenusNotSaidOfOwnDifferentiaeReading isGenus differentiaOf saidOf ∧
  InGenusOnlyUnderAGenusReading isGenus inGenus ∧
  (∀ x, inGenus x .genus ∧ saidOf .genus (speciesOf x) ∧
    saidOf .differentia (speciesOf x)) ∧
  BeingIsNotAGenusReading isGenus .being

/-- Exact equality of the noncausal data in the two q.3 a.4 profiles.
The sole varied field is the efficient cause relation. -/
def SameNoncausalData (p q : Profile Bool Bool Unit) : Prop :=
  p.InAct = q.InAct ∧ p.essenceOf = q.essenceOf ∧
  p.esseOf = q.esseOf ∧
  p.essentialPrinciplesAloneSufficeForEsse =
    q.essentialPrinciplesAloneSufficeForEsse ∧ p.esse = q.esse

/-- Joint controls under the fixed nonvacuous taxonomy:
* an actual distinct-esse subject with no sufficient efficient self-cause can
  lack every efficient esse edge, failing causal exhaustiveness;
* the same noncausal data admit an actual distinct efficient esse cause and
  the two q.3 a.4 premises;
* with the same actuality and taxonomy, an edge-free copy whose represented
  essence and esse coincide satisfies both q.3 a.4 premises vacuously.

The last copy isolates the missing genus-to-real-distinction interface; it
does not satisfy the additional real-composition thesis of q.3 a.5 merely by
being called a genus model. No necessity, pure actuality, full simplicity,
world-indexed causal correspondence or actual applicability is concluded. -/
def Boundary : Prop :=
  Taxonomy ∧
  ∃ p₀ p₁ pᵢ : Profile Bool Bool Unit,
    SameNoncausalData p₀ p₁ ∧
    Coherent p₀ ∧ Coherent p₁ ∧ Coherent pᵢ ∧
    DistinctEsseAt p₀ false ∧ DistinctEsseAt p₁ false ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading p₀ ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading p₁ ∧
    (∀ y x r, ¬p₀.CausesIn y x r) ∧
    ¬HasExternalEsseCause p₀ false ∧
    HasExternalEsseCause p₁ false ∧
    ¬DistinctEsseCauseDichotomyReading p₀ ∧
    DistinctEsseCauseDichotomyReading p₁ ∧
    pᵢ.InAct = p₁.InAct ∧ pᵢ.essenceOf = p₁.essenceOf ∧
    (∀ x, pᵢ.esseOf x = pᵢ.essenceOf x) ∧
    (∀ y x r, ¬pᵢ.CausesIn y x r) ∧
    (∀ x, ¬HasExternalEsseCause pᵢ x) ∧
    DistinctEsseCauseDichotomyReading pᵢ ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading pᵢ ∧
    pᵢ.InAct false pᵢ.esse

end TruthCore.Mereology.GenusCauseBoundary
