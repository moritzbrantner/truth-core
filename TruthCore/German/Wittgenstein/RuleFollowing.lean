/-!
Wittgenstein on rule-following: the shape of the interpretation regress
(*Philosophische Untersuchungen* §§198, 201; #1010).

§198: "Jede Deutung hängt, mitsamt dem Gedeuteten, in der Luft; sie kann ihm
nicht als Stütze dienen. Die Deutungen allein bestimmen die Bedeutung nicht."
§201: the paradox that no course of action could be determined by a rule, and
the diagnosis that "wir in diesem Gedankengang Deutung hinter Deutung setzen",
which shows "daß es eine Auffassung einer Regel gibt, die *nicht* eine
*Deutung* ist".

Vocabulary (stipulative, `DEF-INTERPRETATION-OF-AN-ITEM`,
`DEF-DETERMINED-BY-RULE`): `Item` ranges over applications of a rule and over
interpretations of it (an interpretation is a further expression of the rule,
"einen Ausdruck der Regel durch einen anderen ersetzen", §201); `Interprets i a`
says that `i` is an interpretation of `a`; `Determined a` says that what
accords with the rule at `a` is fixed. Nothing here says what fixes it.

The logical point is the regress: if an item is determined only through a
determined interpretation of it, and interpretations do not go on behind one
another without end, then nothing is determined. Readings differ on which
premise to give up (`DISAMB-RULE-FOLLOWING-PARADOX`): the paradox reading
(Kripke's sceptic) keeps the interpretation premise and denies that any
meaning is determined by a fact; the diagnostic reading (§201's own next
sentence) keeps determination and denies the interpretation premise: some
grasp of a rule is not an interpretation but is shown in practice (§202).
-/

namespace TruthCore.German.Wittgenstein.RuleFollowing

/-- The interpretation premise (`STMT-RULE-DETERMINED-ONLY-THROUGH-INTERPRETATION`):
an item is determined only if some interpretation of it is itself determined.
This is the assumption §201 diagnoses ("jedes Handeln nach der Regel sei ein
Deuten"); it is not attributed to Wittgenstein as his view. -/
def DeterminedOnlyThroughInterpretationReading {Item : Type}
    (Interprets : Item → Item → Prop) (Determined : Item → Prop) : Prop :=
  ∀ a, Determined a → ∃ i, Interprets i a ∧ Determined i

/-- No endless interpretation (`STMT-NO-ENDLESS-INTERPRETATION-REGRESS`): the
relation "is an interpretation of" is well-founded, so there is no infinite
descending chain of interpretations, each behind the last ("Deutung hinter
Deutung"). Lean core `WellFounded`. -/
def NoEndlessInterpretationReading {Item : Type}
    (Interprets : Item → Item → Prop) : Prop :=
  WellFounded Interprets

/-- Some rule-following is determined (`STMT-SOME-RULE-APPLICATION-DETERMINED`):
some item is determined. The diagnostic reading keeps this (we do follow
rules, §202); the paradox reading denies it in the factual sense. -/
def SomeApplicationDeterminedReading {Item : Type} (Determined : Item → Prop) : Prop :=
  ∃ a, Determined a

/-- The regress conclusion (`STMT-NO-RULE-APPLICATION-DETERMINED`): no item is
determined, the first sentence of §201 generalized to every item. -/
def NothingDeterminedReading {Item : Type} (Determined : Item → Prop) : Prop :=
  ∀ a, ¬ Determined a

end TruthCore.German.Wittgenstein.RuleFollowing
