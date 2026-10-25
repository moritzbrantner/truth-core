import TruthCore.Refutations.Emotivism
namespace TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP
open TruthCore.English.VanRoojen
open TruthCore.Refutations.Emotivism

/-- Geach's argument against naive emotivism. Suppose the modus ponens were
valid. By the Frege point, `p` would mean the same free-standing as in the
antecedent. `p` is moral, so it expresses some attitude `a` free-standing. On
the occasion reading of emotivism, occurrences with the same meaning express the
same attitudes, so the antecedent occurrence would express `a` too. But it
does not express it. -/
theorem naiveEmotivismInvalidatesGeachMP {Sentence Ctx Meaning Attitude : Type}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop)
    (ValidMP : Sentence → Sentence → Prop) (free antecedent : Ctx) (p q : Sentence)
    (hEmotivism : EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses)
    (hFree : FreeMoralAssertionExpressesAttitudeReading Moral Expresses free)
    (hAntecedent : AntecedentLacksFreeStandingAttitudeReading Expresses free antecedent p)
    (hFrege : ValidityRequiresConstantMeaningReading ValidMP meaning free antecedent)
    (hMoral : GeachMinorPremiseIsMoralReading Moral p) :
    GeachModusPonensInvalid ValidMP p q := by
  intro hValid
  -- INF-FREGE-POINT-AT-GEACH-MP: validity needs p to mean the same in both places
  have hSame : meaning p free = meaning p antecedent := hFrege p q hValid
  -- INF-GEACH-MINOR-PREMISE-EXPRESSES-ATTITUDE: p is moral, so free-standing it expresses some a
  obtain ⟨a, hExpressed⟩ := hFree p hMoral
  -- INF-NAIVE-EMOTIVISM-ANTECEDENT-EXPRESSES-ATTITUDE: same meaning, same attitudes
  have hInAntecedent : Expresses p antecedent a :=
    hEmotivism p hMoral free antecedent hSame a hExpressed
  -- INF-NAIVE-EMOTIVISM-INVALIDATES-GEACH-MP: but the antecedent does not express a
  exact hAntecedent a hExpressed hInAntecedent

/-! ## Countermodels

Each premise is needed. In every model below one premise fails, the other four
hold, and Geach's modus ponens is valid. There is one sentence, `p = q = ()`;
the contexts are `true` (free-standing) and `false` (antecedent); there is one
attitude. -/

/-- Without the occasion reading of emotivism: meaning is constant, the
free-standing occurrence expresses the attitude and the antecedent does not.
This is the constant-meaning expressivist's model. -/
theorem withoutEmotivistMeaningValid :
    ∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Bool)
      (Expresses : Unit → Bool → Unit → Prop) (ValidMP : Unit → Unit → Prop),
      ¬ EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
      FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
      AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
      ValidityRequiresConstantMeaningReading ValidMP meaning true false ∧
      GeachMinorPremiseIsMoralReading Moral () ∧ ValidMP () () := by
  refine ⟨fun _ => True, fun _ _ => true, fun _ c _ => c = true, fun _ _ => True,
    ?_, ?_, ?_, ?_, trivial, trivial⟩
  · intro h
    exact Bool.noConfusion (h () trivial true false rfl () rfl)
  · exact fun _ _ => ⟨(), rfl⟩
  · exact fun _ _ h => Bool.noConfusion h
  · exact fun _ _ _ => rfl

/-- Without the free-standing expression of an attitude: nothing expresses any
attitude. Emotivism then holds vacuously. -/
theorem withoutFreeExpressionValid :
    ∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Bool)
      (Expresses : Unit → Bool → Unit → Prop) (ValidMP : Unit → Unit → Prop),
      EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
      ¬ FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
      AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
      ValidityRequiresConstantMeaningReading ValidMP meaning true false ∧
      GeachMinorPremiseIsMoralReading Moral () ∧ ValidMP () () := by
  refine ⟨fun _ => True, fun _ _ => true, fun _ _ _ => False, fun _ _ => True,
    ?_, ?_, ?_, ?_, trivial, trivial⟩
  · exact fun _ _ _ _ _ _ h => h
  · intro h
    obtain ⟨_, hFalse⟩ := h () trivial
    exact hFalse
  · exact fun _ h _ => h
  · exact fun _ _ _ => rfl

/-- Without the antecedent's silence: every occurrence expresses the attitude,
embedded or not. -/
theorem withoutSilentAntecedentValid :
    ∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Bool)
      (Expresses : Unit → Bool → Unit → Prop) (ValidMP : Unit → Unit → Prop),
      EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
      FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
      ¬ AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
      ValidityRequiresConstantMeaningReading ValidMP meaning true false ∧
      GeachMinorPremiseIsMoralReading Moral () ∧ ValidMP () () := by
  refine ⟨fun _ => True, fun _ _ => true, fun _ _ _ => True, fun _ _ => True,
    ?_, ?_, ?_, ?_, trivial, trivial⟩
  · exact fun _ _ _ _ _ _ _ => trivial
  · exact fun _ _ => ⟨(), trivial⟩
  · exact fun h => h () trivial trivial
  · exact fun _ _ _ => rfl

/-- Without the Frege point: the sentence means something different in each
kind of occurrence, so emotivism's constraint is idle, and validity is not
tied to constant meaning. -/
theorem withoutFregePointValid :
    ∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Bool)
      (Expresses : Unit → Bool → Unit → Prop) (ValidMP : Unit → Unit → Prop),
      EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
      FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
      AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
      ¬ ValidityRequiresConstantMeaningReading ValidMP meaning true false ∧
      GeachMinorPremiseIsMoralReading Moral () ∧ ValidMP () () := by
  refine ⟨fun _ => True, fun _ c => c, fun _ c _ => c = true, fun _ _ => True,
    ?_, ?_, ?_, ?_, trivial, trivial⟩
  · intro _ _ c c' hSame _ hExpressed
    have hContext : c = c' := hSame
    subst hContext
    exact hExpressed
  · exact fun _ _ => ⟨(), rfl⟩
  · exact fun _ _ h => Bool.noConfusion h
  · intro h
    exact Bool.noConfusion (h () () trivial)

/-- Without the minor premise being moral: no sentence is moral, so neither
emotivism nor the free-standing expression applies to it. -/
theorem withoutMoralMinorPremiseValid :
    ∃ (Moral : Unit → Prop) (meaning : Unit → Bool → Bool)
      (Expresses : Unit → Bool → Unit → Prop) (ValidMP : Unit → Unit → Prop),
      EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses ∧
      FreeMoralAssertionExpressesAttitudeReading Moral Expresses true ∧
      AntecedentLacksFreeStandingAttitudeReading Expresses true false () ∧
      ValidityRequiresConstantMeaningReading ValidMP meaning true false ∧
      ¬ GeachMinorPremiseIsMoralReading Moral () ∧ ValidMP () () := by
  refine ⟨fun _ => False, fun _ _ => true, fun _ c _ => c = true, fun _ _ => True,
    ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact fun _ hMoral => hMoral.elim
  · exact fun _ hMoral => hMoral.elim
  · exact fun _ _ h => Bool.noConfusion h
  · exact fun _ _ _ => rfl
  · exact fun h => h

end TruthCore.Results.Comparison.MoralLanguage.NaiveEmotivismInvalidatesGeachMP
