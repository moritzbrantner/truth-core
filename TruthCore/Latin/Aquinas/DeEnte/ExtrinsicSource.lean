module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-!
# De ente: nature or extrinsic source of a distinct esse (#1629)

Thomas Aquinas, *De ente et essentia* c.3 in the Baur/Koch numbering of the
pinned Corpus Thomisticum witness (`AQUINAS-DE-ENTE-C3-4`, anchor [69874]; this
is c.4 in the Leonine numbering):

> Omne autem quod convenit alicui vel est causatum ex principiis naturae suae,
> sicut risibile in homine, vel advenit ab aliquo principio extrinseco, sicut
> lumen in aere ex influentia solis. Non autem potest esse quod ipsum esse sit
> causatum ab ipsa forma vel quiditate rei (dico sicut a causa efficiente) quia
> sic aliqua res esset sui ipsius causa et aliqua res seipsam in esse
> produceret, quod est impossibile. Ergo oportet quod omnis talis res, cuius
> esse est aliud quam natura sua habeat esse ab alio.

The step from "not self-produced" to "from another" needs a further premise.
The vocabulary-free one is `DistinctEsseHasSomeCause`: every actual distinct
esse has some cause of being; no-self-causation then makes that cause another.
In De ente's own vocabulary it is supplied by an exhaustive disjunction whose
nature disjunct is read in the same (efficient) sense as the rejection. This
module keeps the two readings of the nature disjunct apart (DISAMB nature as
source, `NATURE_SOURCE_1` / `NATURE_SOURCE_2`):

* `NatureSource.fromNature x r` (`NATURE_SOURCE_1`): x's having r is caused
  from the principles of x's own nature, in an unspecified mode. This is the
  literal disjunct; reading it as possibly formal (non-efficient) is the
  analyst's, motivated by the qualifier of the rejection.
* `NatureSource.quiddityEfficientlyCauses x r` (`NATURE_SOURCE_2`): x's own
  form or quiddity is an efficient cause of x's having r ("dico sicut a causa
  efficiente").

The shared q.3 a.4 `Profile` supplies `InAct`, the cause-of-being relation
`CausesIn` (DEF-CAUSE-OF-PERFECTION, mode of causation not fixed by the type),
`essenceOf`, `esseOf` and the `esse` respect, so the witness is the same as
in q.3 a.4. The route concludes `DistinctEsseHasOtherActualCause`: a cause of
being other than x (`c ≠ x` only, not non-constituency) and in act as to
being. It does not conclude the q.3 a.4 statement
`DistinctEsseRequiresExternalCauseReading`, whose prose reads that cause as
efficient: nothing here supplies efficiency, and the vocabulary has no
efficiency predicate on arbitrary causes of being that an open bridge could state. A real distinction is represented,
as in q.3 a.4, by `esseOf x ≠ essenceOf x` in the common `Principle` sort; a
merely conceptual distinction is the case `esseOf x = essenceOf x`, where the
bridge is silent. No modality, time or conservation is built in:
`CausesIn c x esse` is the tenseless cause of being, not a sustaining cause.
-/

@[expose] public section

namespace TruthCore.Latin.Aquinas.DeEnte

open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

variable {B P R : Type}

/-- The two readings of "causatum ex principiis naturae suae" as primitive
parameters. Neither is defined from `CausesIn` or from the other: identifying
a nature's efficient causing with the thing's own causing is the separate
source reading `QuiddityCausingEsseIsSelfCausationReading`, and passing from
the broad reading to the efficient one is the open bridge
`NatureSourcedDistinctEsseIsEfficient`. -/
structure NatureSource (Being Respect : Type) where
  /-- `NATURE_SOURCE_1`: x's having r is caused from the principles of x's own
  nature, mode unspecified (as risibility in man). -/
  fromNature : Being → Respect → Prop
  /-- `NATURE_SOURCE_2`: x's own form or quiddity is an efficient cause of x's
  having r. -/
  quiddityEfficientlyCauses : Being → Respect → Prop

/-- *De ente* c.3 [69874], "omne autem quod convenit alicui vel est causatum ex
principiis naturae suae ... vel advenit ab aliquo principio extrinseco".

Read as: for every x and every respect r that x actually has, x's having r is
caused from the principles of x's nature (`NATURE_SOURCE_1`, mode unspecified)
or some c other than x causes x's having r. "Belongs to" is read as `InAct x r`
and "comes from an extrinsic principle" as `CausesIn c x r` with `c ≠ x`; the
stronger reading of "extrinsic" as not a constituent of x is not used. The
disjunction is not exclusive. -/
def NatureOrExtrinsicSourceReading (p : Profile B P R) (n : NatureSource B R) : Prop :=
  ∀ x r, p.InAct x r → n.fromNature x r ∨ ∃ c, c ≠ x ∧ p.CausesIn c x r

/-- OPEN analyst bridge (attribution deferred), the sense bridge
`NATURE_SOURCE_1` → `NATURE_SOURCE_2` at a distinct esse: if an actual x whose
esse differs from its essence has its esse from the principles of its nature,
then its own quiddity efficiently causes that esse. The source's qualifier
"dico sicut a causa efficiente" marks the sense of the rejection, not this
bridge; that a nature can be a non-efficient (formal) principle of its own
subject's esse is the standard Thomist gloss, not the passage's words.
It is restricted to distinct esse: where esse is the nature, being from the
nature is identity, not efficient causing. -/
def NatureSourcedDistinctEsseIsEfficient (p : Profile B P R) (n : NatureSource B R) : Prop :=
  ∀ x, DistinctEsseAt p x → n.fromNature x p.esse → n.quiddityEfficientlyCauses x p.esse

/-- OPEN analyst premise: the weakest exhaustiveness in De ente's vocabulary
(it entails `DistinctEsseHasSomeCause` with the self-causation reading). Every actual x whose esse differs from its essence has its esse either
efficiently caused by its own quiddity (`NATURE_SOURCE_2`) or caused by some c
other than x. It quantifies only over distinct-esse beings and only over esse. -/
def DistinctEsseNatureOrOtherCause (p : Profile B P R) (n : NatureSource B R) : Prop :=
  ∀ x, DistinctEsseAt p x →
    n.quiddityEfficientlyCauses x p.esse ∨ ∃ c, c ≠ x ∧ p.CausesIn c x p.esse

/-- OPEN analyst premise: the vocabulary-free extra premise of the inference.
Every actual x whose esse differs from its essence has some cause of its esse
(`CausesIn c x esse`, mode unspecified). It does not say the cause is other
than x; no-self-causation supplies that. Brute esse and a non-causal intrinsic
or structural account reject it. -/
def DistinctEsseHasSomeCause (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x → ∃ c, p.CausesIn c x p.esse

/-- *De ente* c.3 [69874], "non autem potest esse quod ipsum esse sit causatum
ab ipsa forma vel quiditate rei (dico sicut a causa efficiente) quia sic aliqua
res esset sui ipsius causa et aliqua res seipsam in esse produceret".

Read as: if x's own quiddity efficiently causes x's esse (`NATURE_SOURCE_2`),
then x causes its own esse (`CausesIn x x esse`). Only the conditional is read
here; "quod est impossibile" is the separate statement that nothing causes its
own being. -/
def QuiddityCausingEsseIsSelfCausationReading (p : Profile B P R) (n : NatureSource B R) :
    Prop :=
  ∀ x, n.quiddityEfficientlyCauses x p.esse → p.CausesIn x x p.esse

/-- The conclusion of the De ente route, with the cause mode-unspecified:
every actual x whose esse differs from its essence has its esse caused
(`CausesIn`, DEF-CAUSE-OF-PERFECTION, no efficiency condition) by some c other
than x (`c ≠ x` only) that is in act as to being. It is kept apart from the
q.3 a.4 statement `DistinctEsseRequiresExternalCauseReading`, whose prose
reads the cause as efficient; no premise here supplies efficiency, and no
bridge to that statement is registered. -/
def DistinctEsseHasOtherActualCause (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x → ∃ c, c ≠ x ∧ p.InAct c p.esse ∧ p.CausesIn c x p.esse

/-! ## Finite controls

Each control is one interpretation on `Bool` (two beings, two principles, one
respect) in which `false` actually exists with esse distinct from its essence.
They are statements about these interpretations only, not about what is
metaphysically possible. -/

/-- Brute-esse surrogate: nothing causes anything and nothing is from its
nature. The self-causation reading, no-self-causation, the actuality of causes
of being and the efficiency bridge hold; the literal disjunction, the weak
exhaustiveness, some-cause and the other-cause conclusion fail. -/
def BruteEsseControl : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧
    QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ x, ¬ p.CausesIn x x p.esse) ∧
    (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    NatureSourcedDistinctEsseIsEfficient p n ∧
    ¬ NatureOrExtrinsicSourceReading p n ∧
    ¬ DistinctEsseNatureOrOtherCause p n ∧
    ¬ DistinctEsseHasSomeCause p ∧
    ¬ DistinctEsseHasOtherActualCause p

/-- Formal-nature surrogate: `false` has its esse from its nature
(`NATURE_SOURCE_1`) without its quiddity efficiently causing it, and nothing
causes anything. The literal De ente disjunction, the self-causation reading,
no-self-causation and the actuality of causes of being all hold; the
efficiency bridge, the weak exhaustiveness, some-cause and the conclusion
fail. `fromNature` is an unconstrained primitive, so "formal" is a label for
any non-efficient nature source, not a model of formal causation: the control
shows that the two nature senses are independent primitives and that the
literal disjunction plus the rejection of efficient self-causation give no
other cause without the efficiency bridge. -/
def FormalNatureControl : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧ n.fromNature false p.esse ∧
    ¬ n.quiddityEfficientlyCauses false p.esse ∧
    NatureOrExtrinsicSourceReading p n ∧
    QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ x, ¬ p.CausesIn x x p.esse) ∧
    (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    ¬ NatureSourcedDistinctEsseIsEfficient p n ∧
    ¬ DistinctEsseNatureOrOtherCause p n ∧
    ¬ DistinctEsseHasSomeCause p ∧
    ¬ DistinctEsseHasOtherActualCause p

/-- Self-cause surrogate: `false` causes its own esse through its quiddity.
Every premise except no-self-causation holds; the conclusion fails. -/
def SelfCauseControl : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧
    NatureOrExtrinsicSourceReading p n ∧
    NatureSourcedDistinctEsseIsEfficient p n ∧
    DistinctEsseNatureOrOtherCause p n ∧
    DistinctEsseHasSomeCause p ∧
    QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    ¬ (∀ x, ¬ p.CausesIn x x p.esse) ∧
    ¬ DistinctEsseHasOtherActualCause p

/-- Unrealized-quiddity surrogate: `false`'s quiddity efficiently causes its
esse but `false` is not thereby a cause of its own esse, and nothing causes
anything. Every input except the self-causation reading (and some-cause,
downstream of it) holds; the
conclusion fails. -/
def UnrealizedQuiddityControl : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧
    NatureOrExtrinsicSourceReading p n ∧
    NatureSourcedDistinctEsseIsEfficient p n ∧
    DistinctEsseNatureOrOtherCause p n ∧
    ¬ DistinctEsseHasSomeCause p ∧
    ¬ QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ x, ¬ p.CausesIn x x p.esse) ∧
    (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    ¬ DistinctEsseHasOtherActualCause p

/-- Nonactual-cause surrogate: `true`, not in act as to being, causes
`false`'s esse. Every premise except the actuality of causes of being holds;
the conclusion fails. -/
def NonactualCauseControl : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧
    NatureOrExtrinsicSourceReading p n ∧
    NatureSourcedDistinctEsseIsEfficient p n ∧
    DistinctEsseNatureOrOtherCause p n ∧
    DistinctEsseHasSomeCause p ∧
    QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ x, ¬ p.CausesIn x x p.esse) ∧
    ¬ (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    ¬ DistinctEsseHasOtherActualCause p

/-- Nonvacuity: one interpretation where every premise of the De ente route
holds, `false` actually exists with distinct esse, and `true`, in act as to
being, causes `false`'s esse, so the conclusion holds. -/
def ReceivedEsseNonvacuity : Prop :=
  ∃ (p : Profile Bool Bool Unit) (n : NatureSource Bool Unit),
    DistinctEsseAt p false ∧
    NatureOrExtrinsicSourceReading p n ∧
    NatureSourcedDistinctEsseIsEfficient p n ∧
    DistinctEsseNatureOrOtherCause p n ∧
    DistinctEsseHasSomeCause p ∧
    QuiddityCausingEsseIsSelfCausationReading p n ∧
    (∀ x, ¬ p.CausesIn x x p.esse) ∧
    (∀ c x, p.CausesIn c x p.esse → p.InAct c p.esse) ∧
    (∃ c, c ≠ false ∧ p.InAct c p.esse ∧ p.CausesIn c false p.esse) ∧
    DistinctEsseHasOtherActualCause p

/-- All six finite controls together. -/
def ExtrinsicSourceControls : Prop :=
  BruteEsseControl ∧ FormalNatureControl ∧ SelfCauseControl ∧
    UnrealizedQuiddityControl ∧ NonactualCauseControl ∧ ReceivedEsseNonvacuity

end TruthCore.Latin.Aquinas.DeEnte
