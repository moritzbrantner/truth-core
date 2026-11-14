module

public import TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

/-!
# SCG I.22 n.4 second case, the dependence sense of *per se necesse*, and n.2/n.6

Analyst reconstruction, with historical attribution **deferred**: no
chapter-specific SCG I.22 corpus passage has been materialized. The public
Latin (la.wikisource oldid 132346) was read as an orientation witness.

`Chapter22Conjunction` formalized n.3 and the **first** case of n.4 with a
modal proxy for n.3's *non per se necesse*. This module adds the **dependence
sense** (`PER_SE_NECESSARY_2`): *per se necesse* means having no cause of its
necessity other than itself (SCG I's *per se* / *per aliud*), and n.3's
non-necessary conjunction is a conjunction which depends on something
(*dependet quantum ad coniunctionem*). It then formalizes, as OPEN premises:

* n.4's **second written case** (*si autem non potest intelligi illud esse
  sine illa essentia, tunc illud esse absolute dependet ab eo a quo dependet
  coniunctio sua ad essentiam illam*);
* n.2's per se clause (*si ab alio dependet, iam non est necesse esse*);
* an analyst coarsening of n.2's consonance trilemma as a **coverage**
  premise for joined distinct principles, with its third horn's accident
  principle (*omne quod sequitur ad esse rei, est ei accidentale*);
* n.6's union-causation principle (*ea quae per se non sunt unum, si
  coniungantur, oportet per aliquam causam uniri*), with *per se unum* kept
  as its own primitive.

The dependence relations are world-independent primitives; only the joining
and the existence of an esse are world-indexed, as in `Chapter22Conjunction`.
The modal sense (`NecessaryEsseAt`) does not occur in any definition here: the
relation between the two senses is not asserted in either direction.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22SecondCase

open TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction

/-- The #1602 profile with the dependence relata of nn.2–6 added. Each new
field is an OPEN primitive (meaning in definition record, not by body):

* `conjunctionDependsOn e q s`: the joining of esse e to proposed quiddity q
  depends on s (n.3's *dependet quantum ad coniunctionem*; n.4's *eo a quo
  dependet coniunctio sua*). It is dependence of the *union*, not of e's being.
* `absolutelyDependsOn e s`: e depends on s for its very being, so that it
  would not be at all unless s were (n.3's *ut omnino non sit nisi illa
  esset*).
* `necessityFrom e s`: s is a cause of e's necessity (*per aliud*).
* `essenceDependsOn q s`: the proposed quiddity q depends on s (n.2 horns
  (ii) and (iii)).
* `perSeOne e q`: e and q are one *per se*, not a union of things that are
  not of themselves one (n.6). -/
structure DependenceProfile (World Being Principle Respect : Type) extends
    TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction.Profile
      World Being Principle Respect where
  conjunctionDependsOn : Principle → Principle → Principle → Prop
  absolutelyDependsOn : Principle → Principle → Prop
  necessityFrom : Principle → Principle → Prop
  essenceDependsOn : Principle → Principle → Prop
  perSeOne : Principle → Principle → Prop

/-- `PER_SE_NECESSARY_2`, the dependence sense: the esse exists at `w` and
nothing other than itself is a cause of its necessity. It does not contain the
modal proxy `NecessaryEsseAt` (`PER_SE_NECESSARY_1`), and it does not exclude
`necessityFrom e e`. -/
def PerSeNecessaryEsseAt (p : DependenceProfile W B P R) (w : W) (e : P) : Prop :=
  p.esseExistsAt w e ∧ ∀ c, c ≠ e → ¬ p.necessityFrom e c

/-- n.3's non-necessary conjunction in the dependence sense: e is joined to q
at `w` and the joining depends on something. It is a sibling of the modal
`ContingentConjunctionAt`; a permanent but dependent union satisfies this and
not that. -/
def DependentConjunctionAt (p : DependenceProfile W B P R) (w : W) (e q : P) : Prop :=
  p.joinedAt w e q ∧ ∃ s, p.conjunctionDependsOn e q s

/-- OPEN, n.4's second written case, attribution deferred: if e is joined to q
and cannot be understood without q, then e depends absolutely on whatever the
joining depends on. -/
def InseparableEsseInheritsConjunctionSource
    (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ e q s, p.joinedAt w e q → ¬ p.conceivableApart e q →
    p.conjunctionDependsOn e q s → p.absolutelyDependsOn e s

/-- OPEN, n.2's per se clause, attribution deferred: an esse which depends
absolutely on something other than itself has its necessity from that other. -/
def DependenceOnAnotherGivesNecessityFromIt (p : DependenceProfile W B P R) : Prop :=
  ∀ e s, p.absolutelyDependsOn e s → s ≠ e → p.necessityFrom e s

/-- OPEN analyst coarsening of n.2's dilemma and consonance trilemma for an
esse joined to a distinct quiddity. Horns (i) and (ii) are kept only in what
they share: the esse, or its joining (n.3's refinement), depends on something
other than the esse. Horn (iii): q depends on e. The repugnance branch is
dropped because a joined pair is one to which the esse belongs. -/
def JoinedDistinctTrilemmaCoverage (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ e q, p.joinedAt w e q → q ≠ e →
    (∃ s, s ≠ e ∧ (p.absolutelyDependsOn e s ∨ p.conjunctionDependsOn e q s)) ∨
    p.essenceDependsOn q e

/-- OPEN, n.2 horn (iii), attribution deferred: what depends on (follows on)
the esse is accidental to it. -/
def ConsequentOfEsseIsAccidental (p : DependenceProfile W B P R) : Prop :=
  ∀ q e, p.essenceDependsOn q e → p.accidentalTo q e

/-- OPEN, n.6's union causation, attribution deferred: a joining of things
which are not one *per se* has some source. Whether distinct principles can
be one *per se* is left to the primitive `perSeOne`. -/
def NonUnifiedUnionHasSource (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ e q, p.joinedAt w e q → ¬ p.perSeOne e q → ∃ s, p.conjunctionDependsOn e q s

/-- Control (a) of the #1602 challenge, stated generally: an inseparable union
of a per se necessary esse with a distinct q cannot depend on q, which is
n.3's own description of the union (n.2 horn (i) returns). -/
def EssenceDependentInseparableUnionExcludedAt
    (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ e q, PerSeNecessaryEsseAt p w e → q ≠ e → p.joinedAt w e q →
    ¬ p.conceivableApart e q → ¬ p.conjunctionDependsOn e q q

/-- Both n.4 cases in the dependence sense: a proposed quiddity whose joining
to the per se necessary esse of an esse-identified bearer depends on
something other than that esse is not that bearer's quiddity. It does not
assert `q = e` or reject the bearer's actual q.3 essence. -/
def DependentConjunctionRejectedAsQuiddityAt
    (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ x s, PerSeNecessaryEsseAt p w (p.q3.esseOf x) →
    p.identifiedWithEsse x (p.q3.esseOf x) →
    p.joinedAt w (p.q3.esseOf x) (p.proposedQuiddityOf x) →
    p.conjunctionDependsOn (p.q3.esseOf x) (p.proposedQuiddityOf x) s →
    s ≠ p.q3.esseOf x →
    ¬ p.isQuiddityOf x (p.proposedQuiddityOf x)

/-- n.2 (coarsened coverage) with nn.3–4: no proposed quiddity distinct from
the per se necessary esse of an esse-identified bearer and joined to it is
that bearer's quiddity. -/
def JoinedDistinctQuiddityRejectedAt
    (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ x, PerSeNecessaryEsseAt p w (p.q3.esseOf x) →
    p.identifiedWithEsse x (p.q3.esseOf x) →
    p.joinedAt w (p.q3.esseOf x) (p.proposedQuiddityOf x) →
    p.proposedQuiddityOf x ≠ p.q3.esseOf x →
    ¬ p.isQuiddityOf x (p.proposedQuiddityOf x)

/-- n.6 with nn.3–4, without coverage: if a genuine quiddity joined to the per
se necessary esse of an esse-identified bearer is not one *per se* with it,
the joining has a source which is not other than the esse (constructively:
`¬ s ≠ e`, not `s = e`). -/
def NonUnifiedQuiddityUnionSelfSourcedAt
    (p : DependenceProfile W B P R) (w : W) : Prop :=
  ∀ x, PerSeNecessaryEsseAt p w (p.q3.esseOf x) →
    p.identifiedWithEsse x (p.q3.esseOf x) →
    p.joinedAt w (p.q3.esseOf x) (p.proposedQuiddityOf x) →
    p.isQuiddityOf x (p.proposedQuiddityOf x) →
    ¬ p.perSeOne (p.q3.esseOf x) (p.proposedQuiddityOf x) →
    ∃ s, p.conjunctionDependsOn (p.q3.esseOf x) (p.proposedQuiddityOf x) s ∧
      ¬ s ≠ p.q3.esseOf x

/-! ## Finite profiles

All extend #1602's `necessaryDistinctProfile`: one bearer, worlds and
principles `Bool`, esse `true` permanently joined to the distinct proposed
quiddity `false`, which is marked genuine quiddity and the represented actual
essence; nothing is conceivable apart or accidental. They differ only in the
new dependence relata. -/

/-- Control (a): n.3's own description, the joining depends on q. -/
def essenceDependentProfile : DependenceProfile Bool Unit Bool Unit :=
  { necessaryDistinctProfile with
    conjunctionDependsOn := fun e q s => e = true ∧ q = false ∧ s = false
    absolutelyDependsOn := fun _ _ => False
    necessityFrom := fun _ _ => False
    essenceDependsOn := fun _ _ => False
    perSeOne := fun _ _ => False }

/-- Control (a) with the second case honoured (e depends absolutely on q) but
n.2's per se clause withheld. -/
def noPerSeClauseProfile : DependenceProfile Bool Unit Bool Unit :=
  { essenceDependentProfile with
    absolutelyDependsOn := fun e s => e = true ∧ s = false }

/-- Control (b): a co-fundamental union, no source, one *per se*. -/
def coFundamentalProfile : DependenceProfile Bool Unit Bool Unit :=
  { essenceDependentProfile with
    conjunctionDependsOn := fun _ _ _ => False
    perSeOne := fun e q => e = true ∧ q = false }

/-- Control (b) with per se unity denied: no source, not one *per se*. -/
def unsourcedNonUnifiedProfile : DependenceProfile Bool Unit Bool Unit :=
  { coFundamentalProfile with perSeOne := fun _ _ => False }

/-- The joining depends only on the esse itself and the pair is not one per se. -/
def selfSourcedProfile : DependenceProfile Bool Unit Bool Unit :=
  { essenceDependentProfile with
    conjunctionDependsOn := fun e q s => e = true ∧ q = false ∧ s = true
    absolutelyDependsOn := fun e s => e = true ∧ s = true }

/-- Horn (iii) holds (q depends on e) but its accident principle is withheld. -/
def noHornThreeAccidentProfile : DependenceProfile Bool Unit Bool Unit :=
  { coFundamentalProfile with
    essenceDependsOn := fun q e => q = false ∧ e = true
    perSeOne := fun _ _ => False }

/-- Nonvacuous positive case: a separable joining dependent on q, so q is
accidental to e and not the quiddity. -/
def separableDependentProfile : DependenceProfile Bool Unit Bool Unit :=
  { essenceDependentProfile with
    q3 := { essenceDependentProfile.q3 with essenceOf := fun _ => true }
    conceivableApart := fun e q => e = true ∧ q = false
    accidentalTo := fun q e => q = false ∧ e = true
    isQuiddityOf := fun _ _ => False }

/-- The full encoded bundle of this module at world `false`. -/
def FullReplyPremisesAt (p : DependenceProfile Bool Unit Bool Unit) : Prop :=
  IntelligibleSeparationMakesAccidental p.toProfile ∧
  AccidentNotQuiddityOfEsseBearer p.toProfile ∧
  InseparableEsseInheritsConjunctionSource p false ∧
  DependenceOnAnotherGivesNecessityFromIt p ∧
  ConsequentOfEsseIsAccidental p ∧
  NonUnifiedUnionHasSource p false

/-- The stable distinct profile of #1602 under the full nn.2–6 bundle, by the
source assigned to its union. These finite assignments test the signature
only; they witness neither metaphysical possibility nor a premise's warrant. -/
def SecondCaseControls : Prop :=
  -- (a) n.3's own q-dependent description: a dependent, not modally
  -- contingent, union; it survives every premise except the second case.
  (PerSeNecessaryEsseAt essenceDependentProfile false true ∧
    DependentConjunctionAt essenceDependentProfile false true false ∧
    ¬ContingentConjunctionAt essenceDependentProfile.toProfile false true false ∧
    essenceDependentProfile.identifiedWithEsse () true ∧
    IntelligibleSeparationMakesAccidental essenceDependentProfile.toProfile ∧
    AccidentNotQuiddityOfEsseBearer essenceDependentProfile.toProfile ∧
    DependenceOnAnotherGivesNecessityFromIt essenceDependentProfile ∧
    ConsequentOfEsseIsAccidental essenceDependentProfile ∧
    JoinedDistinctTrilemmaCoverage essenceDependentProfile false ∧
    NonUnifiedUnionHasSource essenceDependentProfile false ∧
    ¬InseparableEsseInheritsConjunctionSource essenceDependentProfile false ∧
    essenceDependentProfile.isQuiddityOf () false) ∧
  -- (a) with the second case but without n.2's per se clause.
  (PerSeNecessaryEsseAt noPerSeClauseProfile false true ∧
    InseparableEsseInheritsConjunctionSource noPerSeClauseProfile false ∧
    ¬DependenceOnAnotherGivesNecessityFromIt noPerSeClauseProfile ∧
    noPerSeClauseProfile.isQuiddityOf () false) ∧
  -- (b) co-fundamental union: outside both senses of n.3, every premise holds
  -- except coverage, and q is a genuine quiddity distinct from esse.
  (PerSeNecessaryEsseAt coFundamentalProfile false true ∧
    ¬DependentConjunctionAt coFundamentalProfile false true false ∧
    ¬ContingentConjunctionAt coFundamentalProfile.toProfile false true false ∧
    coFundamentalProfile.identifiedWithEsse () true ∧
    FullReplyPremisesAt coFundamentalProfile ∧
    ¬JoinedDistinctTrilemmaCoverage coFundamentalProfile false ∧
    coFundamentalProfile.isQuiddityOf () false ∧
    coFundamentalProfile.q3.esseOf () ≠ coFundamentalProfile.q3.essenceOf ()) ∧
  -- (b) with per se unity denied, n.6 has leverage.
  (PerSeNecessaryEsseAt unsourcedNonUnifiedProfile false true ∧
    ¬NonUnifiedUnionHasSource unsourcedNonUnifiedProfile false ∧
    unsourcedNonUnifiedProfile.isQuiddityOf () false) ∧
  -- Self-sourced union: every premise holds except coverage, the residual
  -- of the n.6 composition.
  (PerSeNecessaryEsseAt selfSourcedProfile false true ∧
    DependentConjunctionAt selfSourcedProfile false true false ∧
    FullReplyPremisesAt selfSourcedProfile ∧
    ¬JoinedDistinctTrilemmaCoverage selfSourcedProfile false ∧
    selfSourcedProfile.isQuiddityOf () false) ∧
  -- Horn (iii) accident principle withheld.
  (PerSeNecessaryEsseAt noHornThreeAccidentProfile false true ∧
    JoinedDistinctTrilemmaCoverage noHornThreeAccidentProfile false ∧
    ¬ConsequentOfEsseIsAccidental noHornThreeAccidentProfile ∧
    noHornThreeAccidentProfile.isQuiddityOf () false) ∧
  -- Positive case: every premise, including coverage, holds and q is
  -- rejected as quiddity.
  (PerSeNecessaryEsseAt separableDependentProfile false true ∧
    DependentConjunctionAt separableDependentProfile false true false ∧
    separableDependentProfile.identifiedWithEsse () true ∧
    FullReplyPremisesAt separableDependentProfile ∧
    JoinedDistinctTrilemmaCoverage separableDependentProfile false ∧
    ¬separableDependentProfile.isQuiddityOf () false)

end TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22SecondCase
