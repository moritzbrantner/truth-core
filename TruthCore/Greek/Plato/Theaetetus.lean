import TruthCore.Logic.SelfApplication

/-!
Plato, *Theaetetus* 169d-172b: the peritropē of Protagoras's measure doctrine
(#397). Witness: `PLATO-THEAET-169`..`PLATO-THEAET-172` (Burnet, PerseusDL).

Socrates argues "from his own account" (170a): what seems to each is so for
the one to whom it seems. Most people oppose any given judgement, thinking it
false (170d); Protagoras, granting that all opine what is, grants the
opponents' contrary opinion about his own thesis to be true (171a-b), so that
his Truth is true "for no one, neither anyone else nor himself" (171c).

The argument is preserved under two readings (`DISAMB-ASSERTED-TRUTH-SENSE`):
with the unqualified truth predicate (horn 1, self-refuting) and with every
"for X" qualifier kept (horn 2, consistent but private). Socrates then retreats
to a restricted doctrine (171d-172b): perceptual qualities, and the just and
holy as each city decrees them, are as they seem; health and advantage are
not, where one judgement differs from another "toward truth" (172a).
-/

namespace TruthCore.Greek.Plato.Theaetetus

open TruthCore.Logic.SelfApplication

variable {Agent Content : Type}

/-- The measure doctrine, relativized (170a): whatever seems so to someone is
true for that one (`STMT-PROTAGORAS-MEASURE-RELATIVE`). Only this direction is
read from 170a. -/
def MeasureDoctrine (Seems : Agent → Content → Prop) (T : TruthSemantics Agent Content) :
    Prop :=
  ∀ a p, Seems a p → T.trueFor a p

/-- Protagoras holds his own thesis: it seems so to him. Not attributed: 171a
states this only as a branch of a conditional ("if he himself believed it").
Derived in the horn results from `AssertsMeasureThesis` and `SincereAsserter`. -/
def HoldsMeasureThesis (Seems : Agent → Content → Prop) (thesis : Content) (a : Agent) :
    Prop :=
  Seems a thesis

/-- Protagoras asserts his thesis: he says it (170a, φησί) and wrote it as his
Truth (171a, ἣν ἐκεῖνος ἔγραψεν) (`STMT-PROTAGORAS-ASSERTS-MEASURE`). -/
def AssertsMeasureThesis (Asserts : Agent → Content → Prop) (thesis : Content) (a : Agent) :
    Prop :=
  Asserts a thesis

/-- Sincerity, an unattributed open premise: whatever the agent asserts seems so
to him (`STMT-PROTAGORAS-SINCERE`). -/
def SincereAsserter (Asserts Seems : Agent → Content → Prop) (a : Agent) : Prop :=
  ∀ p, Asserts a p → Seems a p

/-- Someone opines the denial of the thesis (170d-171a: the many who think it
false) (`STMT-SOMEONE-DENIES-MEASURE`). -/
def SomeoneDeniesThesis (Seems : Agent → Content → Prop) (neg : Content → Content)
    (thesis : Content) : Prop :=
  ∃ b, Seems b (neg thesis)

/-- Unqualified all-opinions-true with explicit scope: every opined content in
scope is true in the unindexed sense (`STMT-PROTAGOREAN-UNQUALIFIED-ALL-OPINIONS-TRUE`). -/
def UnqualifiedAllOpinionsTrue (scope : Content → Prop) (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) : Prop :=
  (Norm.mk scope T.trueAbs).Holds (fun p => ∃ a, Seems a p)

/-- Scope premise of the peritropē (171a, "all opine what is"): the thesis and
its denial both fall under the doctrine (`STMT-PERITROPE-SCOPE`). -/
def PeritropeScope (scope : Content → Prop) (neg : Content → Content) (thesis : Content) :
    Prop :=
  scope thesis ∧ scope (neg thesis)

/-- Horn 1's conclusion (`STMT-PROTAGOREAN-UNQUALIFIED-ALL-OPINIONS-TRUE-FAILS`). -/
def NotUnqualifiedAllOpinionsTrue (scope : Content → Prop) (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) : Prop :=
  ¬ UnqualifiedAllOpinionsTrue scope Seems T

/-- Per-agent negation bridge: a content whose denial is true for an agent is
not true for that agent (`STMT-RELATIVE-NEGATION-RESPECTED`). -/
def RelativeNegationRespected (T : TruthSemantics Agent Content) (neg : Content → Content) :
    Prop :=
  ∀ a p, T.trueFor a (neg p) → ¬ T.trueFor a p

/-- Horn 2's outcome (`STMT-PERITROPE-RELATIVE-HORN-OUTCOME`): the thesis is true
for its holder, and some denier's denial is true for the denier while the
thesis is not true for them, so its truth for the holder gives the denier no
reason in relativist terms (`DEF-REASON-TRANSFER`). -/
def RelativeHornOutcome (T : TruthSemantics Agent Content) (neg : Content → Content)
    (thesis : Content) (a : Agent) : Prop :=
  T.trueFor a thesis ∧ ∃ b, T.trueFor b (neg thesis) ∧ ¬ T.trueFor b thesis

/-- Exempting the denial from the unqualified doctrine is consistent with
everything else horn 1 uses. -/
def PeritropeExemptionConsistent : Prop :=
  ∃ (Seems : Bool → Bool → Prop) (T : TruthSemantics Bool Bool) (neg : Bool → Bool)
    (scope : Bool → Prop) (thesis a : Bool),
    UnqualifiedAllOpinionsTrue scope Seems T ∧ HoldsMeasureThesis Seems thesis a ∧
      SomeoneDeniesThesis Seems neg thesis ∧
      (∀ p, T.trueAbs (neg p) → ¬ T.trueAbs p) ∧ scope thesis ∧ ¬ scope (neg thesis)

/-- The fully relativized premises of horn 2 are jointly consistent, together
with an absolute negation bridge and no absolute truth at all. -/
def PeritropeRelativeConsistent : Prop :=
  ∃ (Seems : Bool → Bool → Prop) (T : TruthSemantics Bool Bool) (neg : Bool → Bool)
    (thesis a : Bool),
    MeasureDoctrine Seems T ∧ RelativeNegationRespected T neg ∧
      HoldsMeasureThesis Seems thesis a ∧ SomeoneDeniesThesis Seems neg thesis ∧
      (∀ p, T.trueAbs (neg p) → ¬ T.trueAbs p) ∧ (∀ p, ¬ T.trueAbs p)

/-- Both peritropē models (`STMT-PERITROPE-MODELS`). -/
def PeritropeModels : Prop :=
  PeritropeExemptionConsistent ∧ PeritropeRelativeConsistent

/-- The restricted doctrine (171d-172b): within the demarcated domain, what
seems so to someone is true for them (`STMT-RESTRICTED-MEASURE`). -/
def RestrictedMeasureDoctrine (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content) : Prop :=
  ∀ a p, D.inDomain p → Seems a p → T.trueFor a p

/-- What the restriction concedes (171e-172a, health and advantage): outside the
domain it is not the case that whatever seems so to someone is true for them
(`STMT-RESTRICTED-MEASURE-CONCESSION`). The denial of the universal, not a
particular case of seeming without truth-for. -/
def RestrictedMeasureConcession (Seems : Agent → Content → Prop)
    (T : TruthSemantics Agent Content) (D : Norm.Demarcation Content) : Prop :=
  ¬ ∀ a p, ¬ D.inDomain p → Seems a p → T.trueFor a p

/-- The unrestricted measure doctrine fails (`STMT-MEASURE-DOCTRINE-FAILS`). -/
def NotMeasureDoctrine (Seems : Agent → Content → Prop) (T : TruthSemantics Agent Content) :
    Prop :=
  ¬ MeasureDoctrine Seems T

end TruthCore.Greek.Plato.Theaetetus
