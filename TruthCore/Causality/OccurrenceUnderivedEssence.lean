import TruthCore.Causality.CogitoNecessaryConcrete
import TruthCore.Causality.UnderivedEssenceEsse

/-! #701: one selected actual world and rigid candidate domain throughout.
No historical attribution: the new support-to-ground map is an open analyst
premise, not evidence that actual existential support is concrete grounding. -/
namespace TruthCore.Causality.OccurrenceUnderivedEssence
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

variable {W B Episode P A : Type}

/-- Every existing R-supporter of an existing concrete target is itself a
concrete ground at the selected world. Stronger than identifying an arbitrary
edge with a cause: it excludes abstract supporters and unmodelled support.
This is an explicit, unattributed, independently disputable bridge. -/
def ActualSupportIsConcreteGround (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (R : W → B → B → Prop) (w : W) : Prop :=
  ∀ c n, m.ontic.ExistsAt w c → m.concrete n → m.ontic.ExistsAt w n →
    R w c n → ActualConcreteGround m w c n

/-- The very same ancestor is actual, concrete, necessary, minimal among
actual concrete grounds, without actual incoming R-support, and has represented
essence–esse identity. No assertion about support at other worlds, uniqueness,
God, or metaphysical adequacy of that identity. -/
def SameWitnessEssenceIdentity (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (R : W → B → B → Prop) (w : W) (p : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile B P A) : Prop :=
  ∃ b e n, Occurs e ∧ Bears b e ∧ GroundAncestor m w n b ∧
    m.concrete n ∧ m.ontic.ExistsAt w n ∧ NecessaryAt m.ontic w n ∧
    (∀ c, ¬ ActualConcreteGround m w c n) ∧
    (∀ c, m.ontic.ExistsAt w c → ¬ R w c n) ∧ p.esseOf n = p.essenceOf n

/-- Reuse #680's SAME ontology and q3 profile; the thought's bearer is the
necessary recipient true, and its ground is the actual necessary source false. -/
def recipientGrounding : TruthCore.Causality.BruteFoundationBoundary.Profile Bool Bool where
  ontic := TruthCore.Models.NecessarilyUnderived.varying
  concrete := fun _ => True
  grounds := TruthCore.Models.NecessarilyUnderived.varyingSupport

def recipientBears (b : Bool) (_ : Unit) : Prop := b = true

/-- All six non-logical #564 premises hold, and the recipient itself satisfies
the old existential necessary-ancestor conclusion, yet that SAME recipient has
incoming support and distinct represented esse. The underived source false
coexists in the same model; this is mathematical satisfiability only. -/
def NecessaryRecipientControl : Prop :=
  let m := recipientGrounding
  let R := TruthCore.Models.NecessarilyUnderived.varyingSupport
  let p := TruthCore.Causality.UnderivedEssenceEsse.pairProfile
  TruthCore.Logic.CogitoSubject.ThoughtOccurs (fun _ : Unit => True) ∧
  TruthCore.Logic.CogitoSubject.EveryThoughtHasSubject (fun _ : Unit => True) recipientBears ∧
  TruthCore.Logic.CogitoConcrete.EveryBearerIsConcrete (fun _ : Unit => True)
    recipientBears m.concrete ∧
  TruthCore.Logic.CogitoConcrete.EveryBearerExistsAt m.ontic (fun _ : Unit => True)
    recipientBears true ∧
  ThinkerGroundingAccessible m (fun _ : Unit => True) recipientBears true ∧
  ThinkerAncestryGrounded m (fun _ : Unit => True) recipientBears true ∧
  NecessaryConcreteAncestorOfThinker m (fun _ : Unit => True) recipientBears true ∧
  NecessaryAt m.ontic true true ∧
  (¬ ∀ c, m.ontic.ExistsAt true c → ¬ R true c true) ∧
  p.esseOf true ≠ p.essenceOf true ∧
  (∀ c, m.ontic.ExistsAt true c → ¬ R true c false) ∧
  p.esseOf false = p.essenceOf false

end TruthCore.Causality.OccurrenceUnderivedEssence
