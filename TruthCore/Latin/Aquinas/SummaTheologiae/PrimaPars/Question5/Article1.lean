/-!
Source-derived reading from Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
(*utrum bonum differat secundum rem ab ente*).

Vocabulary, all of it parameters rather than definitions:

* `Being` — the things quantified over.
* `Perfection` — the perfections (acts) a thing can have.
* `Has x p` — `x` actually has perfection `p` (is in act in that respect).
* `GoodIn x p` — `x` is good in respect of `p`.
* `DesirableIn x p` — `x`, as having `p`, is desirable (*appetibile*): an
  object of appetite in that respect.
* `PerfectIn x p` — `x` is perfect in respect of `p` (lacks nothing of that
  perfection, ST I q.4 a.1 co.). This is perfection in one respect, not the
  universal perfection `TruthCore.Case.Catholicism.IsPerfect` of q.4 a.2, and
  not the "ultimate" perfection that makes a thing good *simpliciter* (ad 1).

The *respondeo* argues in three steps, each formalized below as its own
premise: the notion of good is the desirable; each thing is desirable insofar
as it is perfect; each thing is perfect insofar as it is in act. Its conclusion
is `GoodnessIsActualityReading`. The derivation is result
`AQUINAS-ST-I-Q5-A1-GOODNESS-FROM-DESIRABILITY`; none of the three premises is
a definition here, so the conclusion is not analytic in this vocabulary.

Source witness: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passage `AQUINAS-ST-I-Q5-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Good and being are the same in reality and differ only in concept
(*bonum et ens sunt idem secundum rem: sed differunt secundum rationem tantum*):
a thing is good insofar as it is a being, that is, insofar as it is in act
(*intantum est aliquid bonum, inquantum est ens*).

Formalized per perfection: `x` is good in respect of `p` exactly when it
actually has `p`. The biconditional captures only "the same in reality"
(coextension); the difference in concept (good adds the notion of the
desirable) is not formalized. The reply to the first objection's distinction
between being *simpliciter* and good *simpliciter* is not formalized either.

Source: Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
-/
def GoodnessIsActualityReading {Being : Sort u} {Perfection : Sort v}
    (GoodIn Has : Being → Perfection → Prop) : Prop :=
  ∀ x p, GoodIn x p ↔ Has x p

/-- The notion of good consists in being desirable (*ratio enim boni in hoc
consistit, quod aliquid sit appetibile: unde Philosophus, in I Ethic., dicit
quod bonum est quod omnia appetunt*).

Formalized per perfection: `x` is good in respect of `p` exactly when `x`, as
having `p`, is desirable. Aquinas gives this as the *ratio* (account) of good.
It is kept a premise over two parameters, not a definition of `GoodIn`: were
`GoodIn` defined as `DesirableIn`, this step would be analytic relative to that
definition, and the definition's fidelity would be the open premise instead.
Aristotle's sentence (*Nicomachean Ethics* I.1, 1094a2-3) is about the ends of
arts and actions; the per-perfection application to beings is Aquinas'.

Source: Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
-/
def GoodIsDesirableReading {Being : Sort u} {Perfection : Sort v}
    (GoodIn DesirableIn : Being → Perfection → Prop) : Prop :=
  ∀ x p, GoodIn x p ↔ DesirableIn x p

/-- Each thing is desirable insofar as it is perfect (*manifestum est autem
quod unumquodque est appetibile secundum quod est perfectum: nam omnia appetunt
suam perfectionem*).

Formalized per perfection, with *secundum quod* read as a biconditional, the
same reading the conclusion's *intantum ... inquantum* receives in
`GoodnessIsActualityReading`. Aquinas' reason ("all things desire their own
perfection") supports only the direction from perfect to desirable; the
direction from desirable to perfect rests on the *secundum quod* reading.
Who desires is not formalized.

Source: Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.
-/
def DesirableInsofarAsPerfectReading {Being : Sort u} {Perfection : Sort v}
    (DesirableIn PerfectIn : Being → Perfection → Prop) : Prop :=
  ∀ x p, DesirableIn x p ↔ PerfectIn x p

/-- Each thing is perfect insofar as it is in act (*intantum est autem
perfectum unumquodque, inquantum est actu*; q.4 a.1 co.: *secundum hoc enim
dicitur aliquid esse perfectum, secundum quod est actu*).

Formalized per perfection as a biconditional: `x` is perfect in respect of `p`
exactly when it actually has `p`. q.4 a.1 co. explains *perfectum* as that to
which nothing is lacking according to the mode of its perfection; ad 1 extends
the name to whatever does not lack being in act. The premise is about
perfection in one respect, not universal perfection (q.4 a.2) and not the
ultimate perfection of q.5 a.1 ad 1.

Source: Thomas Aquinas, *Summa theologiae* I q.5 a.1 co.; I q.4 a.1 co.
-/
def PerfectInsofarAsInActReading {Being : Sort u} {Perfection : Sort v}
    (PerfectIn Has : Being → Perfection → Prop) : Prop :=
  ∀ x p, PerfectIn x p ↔ Has x p

/-- Each premise of the q.5 a.1 derivation is needed, and the three are jointly
satisfiable with something good. For each premise there is a model of the other
two over `Unit` in which `GoodnessIsActualityReading` fails; the last conjunct
is a model of all three in which something is good. A formal metastatement, not
a source reading. -/
def GoodnessFromDesirabilityPremisesNeeded : Prop :=
  (¬ ∀ (Being Perfection : Type) (GoodIn DesirableIn PerfectIn Has : Being → Perfection → Prop),
      DesirableInsofarAsPerfectReading DesirableIn PerfectIn →
      PerfectInsofarAsInActReading PerfectIn Has →
      GoodnessIsActualityReading GoodIn Has) ∧
  (¬ ∀ (Being Perfection : Type) (GoodIn DesirableIn PerfectIn Has : Being → Perfection → Prop),
      GoodIsDesirableReading GoodIn DesirableIn →
      PerfectInsofarAsInActReading PerfectIn Has →
      GoodnessIsActualityReading GoodIn Has) ∧
  (¬ ∀ (Being Perfection : Type) (GoodIn DesirableIn PerfectIn Has : Being → Perfection → Prop),
      GoodIsDesirableReading GoodIn DesirableIn →
      DesirableInsofarAsPerfectReading DesirableIn PerfectIn →
      GoodnessIsActualityReading GoodIn Has) ∧
  (∃ GoodIn DesirableIn PerfectIn Has : Unit → Unit → Prop,
      GoodIsDesirableReading GoodIn DesirableIn ∧
      DesirableInsofarAsPerfectReading DesirableIn PerfectIn ∧
      PerfectInsofarAsInActReading PerfectIn Has ∧ GoodIn () ())

end TruthCore.Latin.Aquinas.SummaTheologiae
