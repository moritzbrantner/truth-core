/-!
Aristotle, *Metaphysics* III.3, 998b22-27: neither being nor one can be a
single genus of beings (issue #340).

The text (Ross/Perseus Greek, passage `ARIST-MET-III-3`):

> οὐχ οἷόν τε δὲ τῶν ὄντων ἓν εἶναι γένος οὔτε τὸ ἓν οὔτε τὸ ὄν· ἀνάγκη μὲν
> γὰρ τὰς διαφορὰς ἑκάστου γένους καὶ εἶναι καὶ μίαν εἶναι ἑκάστην, ἀδύνατον
> δὲ κατηγορεῖσθαι ἢ τὰ εἴδη τοῦ γένους ἐπὶ τῶν οἰκείων διαφορῶν ἢ τὸ γένος
> ἄνευ τῶν αὐτοῦ εἰδῶν, ὥστʼ εἴπερ τὸ ἓν γένος ἢ τὸ ὄν, οὐδεμία διαφορὰ οὔτε
> ὂν οὔτε ἓν ἔσται.

The passage stands inside an aporia (Book III raises difficulties on both
sides); the claims attribute the argument to Aristotle as he states it here,
not as his settled doctrine. Aquinas repeats it as Aristotle's demonstration in
ST I q.3 a.5 co. (*omne enim genus habet differentias quae sunt extra essentiam
generis; nulla autem differentia posset inveniri, quae esset extra ens*).

Vocabulary, all parameters (a *typed predication structure*; nothing makes
`SaidOf` an order or a set inclusion):

* `Term` — the predicables: genera, differentiae, species, and being itself.
* `IsGenus g` — `g` is a genus in the strict sense (`DEF-GENUS-STRICT`): a
  predicable said of its species in what they are and divided into them by
  differentiae.
* `DifferentiaOf d g` — `d` is one of the differentiae of the genus `g`.
* `SaidOf t s` — `t` is predicated of `s` as belonging to what `s` is (`s` *is*
  a `t`, not merely accidentally). The *same* relation is used in the premise
  that the genus is not predicated of its differentiae and in the premise that
  each differentia is a being; `DISAMB-PREDICATION-OF-DIFFERENTIA` records why
  and what follows if the two uses differ.
* `ens` — the term *being* (τὸ ὄν). The argument for *one* (τὸ ἕν) is the same
  theorem instantiated at that term; it is not stated separately.

Source: Aristotle, *Metaphysics* III.3 (Bekker pagination), passage
`ARIST-MET-III-3`. CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/

namespace TruthCore.Greek.Aristotle.Metaphysics

universe u

/-- Every genus has a differentia (Aquinas, ST I q.3 a.5 co., second proof:
*omne enim genus habet differentias*). Aristotle presupposes it in 998b22-24,
where the differentiae *of each genus* must be and be one; a genus is divided
into species by its differentiae.

Only existence of at least one differentia is asserted. -/
def EveryGenusHasADifferentiaReading {Term : Sort u}
    (IsGenus : Term → Prop) (DifferentiaOf : Term → Term → Prop) : Prop :=
  ∀ g, IsGenus g → ∃ d, DifferentiaOf d g

/-- The differentiae of each genus are beings (*Metaphysics* III.3, 998b23-24:
ἀνάγκη μὲν γὰρ τὰς διαφορὰς ἑκάστου γένους καὶ εἶναι καὶ μίαν εἶναι ἑκάστην;
Aquinas, ST I q.3 a.5 co.: *non ens non potest esse differentia*).

Read as: being is said (`SaidOf`) of every differentia of every genus. Only the
clause for being is formalized; the parallel clause "and each is one" gives the
same premise for the term *one*. -/
def DifferentiaeAreBeingsReading {Term : Sort u}
    (IsGenus : Term → Prop) (DifferentiaOf SaidOf : Term → Term → Prop)
    (ens : Term) : Prop :=
  ∀ g d, IsGenus g → DifferentiaOf d g → SaidOf ens d

/-- A genus is not predicated of its own differentiae (*Metaphysics* III.3,
998b24-26: ἀδύνατον δὲ κατηγορεῖσθαι ... τὸ γένος ἄνευ τῶν αὐτοῦ εἰδῶν [ἐπὶ τῶν
οἰκείων διαφορῶν]; Aquinas, ST I q.3 a.5 co.: the differentiae *sunt extra
essentiam generis*).

Only the clause about the genus is formalized; the parallel clause that the
species are not predicated of the differentiae is not used. *Without its
species* (ἄνευ τῶν αὐτοῦ εἰδῶν) is read as: of the differentia taken by itself,
which is what `SaidOf g d` says. -/
def GenusNotSaidOfOwnDifferentiaeReading {Term : Sort u}
    (IsGenus : Term → Prop) (DifferentiaOf SaidOf : Term → Term → Prop) :
    Prop :=
  ∀ g d, IsGenus g → DifferentiaOf d g → ¬ SaidOf g d

/-- Being is not a genus (*Metaphysics* III.3, 998b22: οὐχ οἷόν τε δὲ τῶν ὄντων
ἓν εἶναι γένος ... οὔτε τὸ ὄν; Aquinas, ST I q.3 a.5 co.: *ens non potest esse
genus alicuius*).

Strict sense of genus only (`DEF-GENUS-STRICT`). It says nothing about whether
being is a *genus* in the broad sense of a perfection admitting more and less
(`DEF-GENUS-BROAD`, ST I q.2 a.3, quarta via). -/
def BeingIsNotAGenusReading {Term : Sort u} (IsGenus : Term → Prop)
    (ens : Term) : Prop :=
  ¬ IsGenus ens

end TruthCore.Greek.Aristotle.Metaphysics
