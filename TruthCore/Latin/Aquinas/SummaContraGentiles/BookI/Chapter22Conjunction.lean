module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
public import TruthCore.Causality.ActualUnderivedEssenceEsse

/-!
# The contingent-conjunction objection in SCG I.22 nn.3–4

Analyst reconstruction, with historical attribution **deferred** until the
chapter has a verified corpus passage. Aquinas explicitly entertains an esse
that is necessary through itself while its conjunction with a proposed essence
is not necessary (n.3), and replies that, if this esse can be understood apart
from the essence, the latter is accidental to the esse, hence not the quiddity
of the first necessary being, which is that esse (n.4).

The selected-world modal test below is an *analyst proxy* for the non-necessary
conjunction. It is **not** Aquinas's `potest intelligi` by definition. The
world-to-intelligibility bridge stays explicit and independently defeasible.
`identifiedWithEsse` is likewise an open ontic identification, not a modal
coextension or an equality between different Lean sorts. A positive result
rejects only the contingent *conjunction as the first bearer's quiddity*, not
every possible distinct essence–esse account, nor the rival's conjunction as
an accident of the first bearer or essence of a posterior composite.

The existing q.3 a.4 `Profile` supplies `esseOf` and the bearer's represented
actual `essenceOf` rather than duplicating them. A separate `proposedQuiddityOf`
names the *challenged* q, so denying that q is a true quiddity does not deny
the proper essence of the existing bearer. The correspondence of a successful
proposal with `q3.essenceOf` is a further semantic obligation, not encoded in
the contested candidate's name.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- The first two fields deliberately distinguish a bearer and an act of esse.
`joinedAt` is an attachment of an esse to a proposed quiddity, not the
existence of the esse itself; `conceivableApart` is conceptual separability,
not identified with accessibility. `accidentalTo` is an ontological status
relative to the esse, not an accidental proposition or chance event. -/
structure Profile (World Being Principle Respect : Type) where
  q3 : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile
    Being Principle Respect
  proposedQuiddityOf : Being → Principle
  access : World → World → Prop
  esseExistsAt : World → Principle → Prop
  joinedAt : World → Principle → Principle → Prop
  conceivableApart : Principle → Principle → Prop
  accidentalTo : Principle → Principle → Prop
  identifiedWithEsse : Being → Principle → Prop
  isQuiddityOf : Being → Principle → Prop

/-- Necessity here attaches to the *esse principle*, not to a bearer at all
worlds; no grounding or efficient-cause predicate appears in this condition. -/
def NecessaryEsseAt (p : Profile W B P R) (w : W) (e : P) : Prop :=
  p.esseExistsAt w e ∧ ∀ v, p.access w v → p.esseExistsAt v e

/-- The union is present at w but absent at an accessible world. This does
not mean that the esse itself fails to exist at that world. -/
def ContingentConjunctionAt (p : Profile W B P R)
    (w : W) (e q : P) : Prop :=
  p.joinedAt w e q ∧ ∃ v, p.access w v ∧ ¬ p.joinedAt v e q

/-- A precise world-indexed separation witness: the esse still exists in
the counterworld in which the proposed joining does not. -/
def ModalSeparationAt (p : Profile W B P R)
    (w : W) (e q : P) : Prop :=
  p.joinedAt w e q ∧
    ∃ v, p.access w v ∧ p.esseExistsAt v e ∧ ¬ p.joinedAt v e q

/-- The independent structural part of n.3: in a contingent *joining* of
necessary esse, the missing union at another world does not remove esse.
It is false for an esse that disappears with the union. -/
def NecessityAndContingentJoinSeparateAt
    (p : Profile W B P R) (w : W) : Prop :=
  ∀ e q, NecessaryEsseAt p w e →
    ContingentConjunctionAt p w e q → ModalSeparationAt p w e q

/-- OPEN analyst interface. A modal witness of an esse without a union is
claimed to warrant intelligibility of that esse without that quiddity.
This bridge may fail if metaphysical possibility and conceivability diverge. -/
def WorldSeparationShowsIntelligibilityAt
    (p : Profile W B P R) (w : W) : Prop :=
  ∀ e q, ModalSeparationAt p w e q → p.conceivableApart e q

/-- The source's n.4 conditional, separately exposed as an OPEN premise:
intelligibility of esse without q makes q accidental *to that esse*. -/
def IntelligibleSeparationMakesAccidental (p : Profile W B P R) : Prop :=
  ∀ e q, p.conceivableApart e q → p.accidentalTo q e

/-- The other substantive n.4 step is quiddity/accident incompatibility
for a subject ontically identified with its esse. For a bearer which only
*has* that esse, it does not rule out q being the bearer's own quiddity. -/
def AccidentNotQuiddityOfEsseBearer (p : Profile W B P R) : Prop :=
  ∀ x q, p.identifiedWithEsse x (p.q3.esseOf x) →
    p.accidentalTo q (p.q3.esseOf x) → ¬ p.isQuiddityOf x q

/-- A total profile control will use this exact bundle, so the last step
cannot hide the conceptual bridge in a definition of "self-necessary". -/
def ContingentReplyPremisesAt (p : Profile W B P R) (w : W) : Prop :=
  WorldSeparationShowsIntelligibilityAt p w ∧
  IntelligibleSeparationMakesAccidental p ∧
  AccidentNotQuiddityOfEsseBearer p

/-- The selected result of nn.3–4: a self-necessary esse whose conjunction
to q is contingent can have q attached, but under the three OPEN
interpretive/ontic premises q is not the quiddity of the first bearer
identified with that esse. It does **not** prove `q = e`; necessary attachment
and distinct but co-fundamental principles remain outside this rebuttal. -/
def ContingentConjunctionRejectedAsQuiddityAt
    (p : Profile W B P R) (w : W) : Prop :=
  ∀ x, NecessaryEsseAt p w (p.q3.esseOf x) →
    p.identifiedWithEsse x (p.q3.esseOf x) →
    ContingentConjunctionAt p w (p.q3.esseOf x) (p.proposedQuiddityOf x) →
    ¬ p.isQuiddityOf x (p.proposedQuiddityOf x)

/-- The finite witnesses below use one bearer, two represented principles,
and two worlds. The conceptual predicate is independently assigned, so a
counterworld cannot make it true by definitional fiat. -/
def contingentProfile : Profile Bool Unit Bool Unit where
  q3 := {
    InAct := fun _ _ => True
    CausesIn := fun _ _ _ => False
    essenceOf := fun _ => true
    esseOf := fun _ => true
    essentialPrinciplesAloneSufficeForEsse := fun _ => False
    esse := () }
  proposedQuiddityOf := fun _ => false
  access := fun _ _ => True
  esseExistsAt := fun _ e => e = true
  joinedAt := fun w e q => w = false ∧ e = true ∧ q = false
  conceivableApart := fun e q => e = true ∧ q = false
  accidentalTo := fun q e => q = false ∧ e = true
  identifiedWithEsse := fun _ e => e = true
  isQuiddityOf := fun _ _ => False

def noIntelligibilityProfile : Profile Bool Unit Bool Unit :=
  { contingentProfile with
    q3 := { contingentProfile.q3 with essenceOf := fun _ => false }
    conceivableApart := fun _ _ => False
    accidentalTo := fun _ _ => False
    isQuiddityOf := fun _ q => q = false }

def noAccidentBridgeProfile : Profile Bool Unit Bool Unit :=
  { contingentProfile with
    q3 := { contingentProfile.q3 with essenceOf := fun _ => false }
    accidentalTo := fun _ _ => False
    isQuiddityOf := fun _ q => q = false }

def noQuiddityCriterionProfile : Profile Bool Unit Bool Unit :=
  { contingentProfile with
    q3 := { contingentProfile.q3 with essenceOf := fun _ => false }
    isQuiddityOf := fun _ q => q = false }

def nonEsseBearerProfile : Profile Bool Unit Bool Unit :=
  { noQuiddityCriterionProfile with identifiedWithEsse := fun _ _ => False }

def noNecessaryEsseProfile : Profile Bool Unit Bool Unit :=
  { noIntelligibilityProfile with esseExistsAt := fun w e => w = false ∧ e = true }

/-- A separate, permanently joined q may be a quiddity although its
represented principle differs from e. The n.3–4 reply has no leverage over
this case; the n.2 trilemma is an additional open argument, not a corollary. -/
def necessaryDistinctProfile : Profile Bool Unit Bool Unit :=
  { contingentProfile with
    q3 := { contingentProfile.q3 with essenceOf := fun _ => false }
    joinedAt := fun _ e q => e = true ∧ q = false
    conceivableApart := fun _ _ => False
    accidentalTo := fun _ _ => False
    isQuiddityOf := fun _ q => q = false }

/-- An actual, necessary, support-underived bearer on the SAME two-world
carrier as `necessaryDistinctProfile`. Empty support means underivedness is
not smuggled in via a different existential witness. This does not model
SCG's rich `per se` necessity or the n.2 dependency trilemma. -/
def stableDistinctOntic :
    TruthCore.German.Kant.CosmologicalInference.Ontic Bool Unit where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ _ _ => False

def stableDistinctSupport (_ : Bool) (_ _ : Unit) : Prop := False

/-- The bare D → E inference is false under the reused D and E signatures:
actual existence, de re necessity, and no actual supporter all hold for the
one bearer, but represented principles differ, and the n.3–4 premises do not
resolve the permanently joined distinct-principles case. -/
def UnderivedDistinctBoundary : Prop :=
  let m := stableDistinctOntic
  m.ExistsAt false () ∧
  TruthCore.German.Kant.CosmologicalInference.NecessaryAt m false () ∧
  TruthCore.Causality.NecessarilyUnderived.NoExistingSupportAt
    m stableDistinctSupport false () ∧
  ContingentReplyPremisesAt necessaryDistinctProfile false ∧
  necessaryDistinctProfile.isQuiddityOf () false ∧
  necessaryDistinctProfile.identifiedWithEsse () true ∧
  necessaryDistinctProfile.q3.esseOf () ≠ necessaryDistinctProfile.q3.essenceOf () ∧
  ¬ TruthCore.Causality.ActualUnderivedEssenceEsse.ActualUnderivedEssenceIdentity
    m stableDistinctSupport false necessaryDistinctProfile.q3

/-- Nonvacuous positive case, omissions of each of the three bridge steps,
the explicit self-esse identification and esse necessity, and a stable-union
distinct-essence alternative. The models only test this signature; they do
not witness metaphysical possibility or independently defend a premise. -/
def Controls : Prop :=
  (NecessaryEsseAt contingentProfile false true ∧
    ContingentConjunctionAt contingentProfile false true false ∧
    contingentProfile.identifiedWithEsse () true ∧
    ContingentReplyPremisesAt contingentProfile false ∧
    ¬contingentProfile.isQuiddityOf () false) ∧
  (NecessaryEsseAt noIntelligibilityProfile false true ∧
    ContingentConjunctionAt noIntelligibilityProfile false true false ∧
    noIntelligibilityProfile.identifiedWithEsse () true ∧
    ¬WorldSeparationShowsIntelligibilityAt noIntelligibilityProfile false ∧
    IntelligibleSeparationMakesAccidental noIntelligibilityProfile ∧
    AccidentNotQuiddityOfEsseBearer noIntelligibilityProfile ∧
    noIntelligibilityProfile.isQuiddityOf () false) ∧
  (NecessaryEsseAt noAccidentBridgeProfile false true ∧
    ContingentConjunctionAt noAccidentBridgeProfile false true false ∧
    noAccidentBridgeProfile.identifiedWithEsse () true ∧
    WorldSeparationShowsIntelligibilityAt noAccidentBridgeProfile false ∧
    ¬IntelligibleSeparationMakesAccidental noAccidentBridgeProfile ∧
    AccidentNotQuiddityOfEsseBearer noAccidentBridgeProfile ∧
    noAccidentBridgeProfile.isQuiddityOf () false) ∧
  (NecessaryEsseAt noQuiddityCriterionProfile false true ∧
    ContingentConjunctionAt noQuiddityCriterionProfile false true false ∧
    noQuiddityCriterionProfile.identifiedWithEsse () true ∧
    WorldSeparationShowsIntelligibilityAt noQuiddityCriterionProfile false ∧
    IntelligibleSeparationMakesAccidental noQuiddityCriterionProfile ∧
    ¬AccidentNotQuiddityOfEsseBearer noQuiddityCriterionProfile ∧
    noQuiddityCriterionProfile.isQuiddityOf () false) ∧
  (NecessaryEsseAt nonEsseBearerProfile false true ∧
    ContingentConjunctionAt nonEsseBearerProfile false true false ∧
    ¬nonEsseBearerProfile.identifiedWithEsse () true ∧
    ContingentReplyPremisesAt nonEsseBearerProfile false ∧
    nonEsseBearerProfile.isQuiddityOf () false) ∧
  (¬NecessaryEsseAt noNecessaryEsseProfile false true ∧
    ContingentConjunctionAt noNecessaryEsseProfile false true false ∧
    noNecessaryEsseProfile.identifiedWithEsse () true ∧
    ContingentReplyPremisesAt noNecessaryEsseProfile false ∧
    noNecessaryEsseProfile.isQuiddityOf () false) ∧
  (NecessaryEsseAt necessaryDistinctProfile false true ∧
    necessaryDistinctProfile.identifiedWithEsse () true ∧
    ContingentReplyPremisesAt necessaryDistinctProfile false ∧
    ¬ContingentConjunctionAt necessaryDistinctProfile false true false ∧
    necessaryDistinctProfile.isQuiddityOf () false ∧
    necessaryDistinctProfile.q3.esseOf () ≠ necessaryDistinctProfile.q3.essenceOf ())

end TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction
