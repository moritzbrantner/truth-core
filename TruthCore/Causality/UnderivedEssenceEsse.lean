import TruthCore.Causality.UnderivedNonComposite
import TruthCore.Causality.ExistenceActuality
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-! A conditional same-witness connection for #319. The q.3 a.4 first-proof
premises retain their existing source readings. Actuality and causal/support
interfaces are explicitly open; no modal necessity, pure actuality, uniqueness
or self-explanation follows merely from equality in the Principle sort. -/
namespace TruthCore.Causality.UnderivedEssenceEsse
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.UnderivedCommonSource
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Causality.ExistenceActuality
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- The SAME actual, necessary, globally R-underived bearer has identical
represented essence and esse. This does not identify it with God or establish
that its Principle identity supplies an adequate intrinsic explanation. -/
def UnderivedEssenceIdentity {W B P A : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A) : Prop :=
  ∃ n, NamedNecessarilyUnderived m R w n ∧ p.esseOf n = p.essenceOf n

/-- Atemporal q.3 profile of the already registered `varying` model at world
true. Its actual cause false→true has actual relata. Both beings are modally
necessary; the recipient true has distinct essence and esse. This profile is
an analyst control, not a metaphysically possible caused necessary being. -/
def pairProfile : Profile Bool Bool Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c = false ∧ x = true
  essenceOf := fun _ => false
  esseOf := id
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- The same Ontic source false is omitted from q.3's actual extension, while
true remains q.3-actual. This violates only the new existence→actuality adapter
among the displayed interface conditions, not by making either carrier empty. -/
def mismatchedActuality : Profile Bool Bool Unit where
  InAct := fun x _ => x = true
  CausesIn := fun _ _ _ => False
  essenceOf := id
  esseOf := fun _ => true
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

/-- Three fixed-model controls: (1) the bridge's actual underived source and
its necessary-but-caused recipient in ONE interpretation; (2) actuality
mismatch blocks propagation to that named source; (3) withholding the ordinary
cause→R map leaves the named target underived relative to empty R although it
has an actual efficient cause. The omissions concern named propagation, not
inclusion-minimality of every premise in the existential union theorem. -/
def Controls : Prop :=
  let m := TruthCore.Models.NecessarilyUnderived.varying
  (∀ w v, m.frame.access w v) ∧ (∀ w x, m.ExistsAt w x) ∧
  (∀ w, TruthCore.Causality.NecessarilyUnderived.WellFoundedPresentEsseSupport
    m m.Causes w) ∧
  (Coherent pairProfile ∧ DistinctEsseCauseDichotomyReading pairProfile ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading pairProfile ∧
    ExistingInActAt m pairProfile.InAct pairProfile.esse true ∧
    UnitingCausesPresent m pairProfile.CausesIn pairProfile.esse true ∧
    UnitingCausesAreActual m pairProfile.CausesIn pairProfile.esse true ∧
    ActualCauseSupportsEsse m m.Causes true ∧
    NamedNecessarilyUnderived m m.Causes true false ∧
    pairProfile.esseOf false = pairProfile.essenceOf false ∧
    NecessaryAt m true true ∧ HasExternalEsseCause pairProfile true ∧
    DistinctEsseAt pairProfile true ∧
    ¬ NamedNecessarilyUnderived m m.Causes true true) ∧
  (Coherent mismatchedActuality ∧
    DistinctEsseCauseDichotomyReading mismatchedActuality ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading mismatchedActuality ∧
    UnitingCausesPresent m mismatchedActuality.CausesIn () true ∧
    UnitingCausesAreActual m mismatchedActuality.CausesIn () true ∧
    ActualCauseSupportsEsse m m.Causes true ∧
    NamedNecessarilyUnderived m m.Causes true false ∧
    ¬ ExistingInActAt m mismatchedActuality.InAct () true ∧
    mismatchedActuality.esseOf false ≠ mismatchedActuality.essenceOf false) ∧
  (Coherent pairProfile ∧ DistinctEsseCauseDichotomyReading pairProfile ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading pairProfile ∧
    ExistingInActAt m pairProfile.InAct () true ∧
    UnitingCausesPresent m pairProfile.CausesIn () true ∧
    UnitingCausesAreActual m pairProfile.CausesIn () true ∧
    NamedNecessarilyUnderived m (fun _ _ _ => False) true true ∧
    ¬ ActualCauseSupportsEsse m (fun _ _ _ => False) true ∧
    pairProfile.esseOf true ≠ pairProfile.essenceOf true)

/-- Three actual individuals, with an esse-cause none→some false and an
ordinary event-cause some false→some true. Both edges are world-local and the
ordinary graph is a finite DAG; only the first edge supports esse. -/
def typedOnlyOntic : Ontic Unit (Option Bool) where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ c x => (c = none ∧ x = some false) ∨
    (c = some false ∧ x = some true)

def typedOnlySupport (_ : Unit) (c x : Option Bool) : Prop :=
  c = none ∧ x = some false

def typedOnlyProfile : Profile (Option Bool) (Option Bool) Unit where
  InAct := fun _ _ => True
  CausesIn := fun c x _ => c = none ∧ x = some false
  essenceOf := id
  esseOf := fun x => match x with | some false => none | other => other
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

def typedOnlyRank : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- The direct typed esse-cause correspondence can hold with the displayed q3 and
source properties, while the broader ordinary-cause→R interface fails on an
actual event edge. No claim that the displayed assignments describe a real
possible cosmos is made. -/
def TypedCorrespondenceControl : Prop :=
  Coherent typedOnlyProfile ∧
  DistinctEsseCauseDichotomyReading typedOnlyProfile ∧
  EssentialPrinciplesCannotCauseDistinctEsseReading typedOnlyProfile ∧
  ExistingInActAt typedOnlyOntic typedOnlyProfile.InAct () () ∧
  UnitingCausesPresent typedOnlyOntic typedOnlyProfile.CausesIn () () ∧
  TruthCore.Causality.ExistenceActuality.ActualEsseCausesSupportAt
    typedOnlyOntic typedOnlySupport typedOnlyProfile.CausesIn () () ∧
  UnitingCausesAreActual typedOnlyOntic typedOnlyProfile.CausesIn () () ∧
  ¬ ActualCauseSupportsEsse typedOnlyOntic typedOnlySupport () ∧
  TruthCore.Causality.NecessarilyUnderived.WellFoundedUnionNecessarySupport
    typedOnlyOntic typedOnlySupport () ∧
  WellFounded (typedOnlyOntic.Causes ()) ∧
  UnderivedEssenceIdentity typedOnlyOntic typedOnlySupport () typedOnlyProfile

/-- Original named-propagation controls plus the direct-interface strictness
control. This separate package preserves the original frozen Controls type. -/
def ExtendedControls : Prop := Controls ∧ TypedCorrespondenceControl
end TruthCore.Causality.UnderivedEssenceEsse
