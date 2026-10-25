/-!
Answer maps and the collapse lemma (#185; owner method of 2026-10-24 on #181).

A theory's answer map says, for each shared question, whether the theory
answers it and which proposition it gives as its answer (owner decision on
#149: a theory is a set of propositions and arguments, so an answer is a
proposition). A question the theory does not answer is *unexplained*.

A "mimic" theory (quasi-realism, expressivism) tries to earn every answer of
realism. The collapse lemma says what happens if it succeeds everywhere: it is
not a distinct rival, and it inherits every commitment of realism, including
realism's answer to the grounding question. So a mimic is a distinct rival only
through some question where it deviates, and each deviation is a target.

Matching requires the same answer availability and, only where an answer is
given, equivalence of the answers (`↔`), not identity: identity of
propositions would need propositional extensionality, an axiom the results here
do not use.
-/

namespace TruthCore.Metaethics

/-- A theory's answer map over the shared questions `Q`. -/
structure AnswerMap (Q : Type) where
  /-- The theory answers `q` (rather than leaving it unexplained). -/
  answers : Q → Prop
  /-- The proposition the theory gives as its answer to `q`; ignored when
  `answers q` does not hold. -/
  says : Q → Prop

/-- `T` matches `R` on `q`: it answers `q` exactly when `R` does, and its
answer is equivalent to `R`'s when it answers. Unused contents do not
distinguish maps that both leave the question unexplained. -/
def Matches {Q : Type} (T R : AnswerMap Q) (q : Q) : Prop :=
  (T.answers q ↔ R.answers q) ∧ (T.answers q → (T.says q ↔ R.says q))

/-- `T` mimics `R`: it matches `R` on every shared question. -/
def Mimics {Q : Type} (T R : AnswerMap Q) : Prop :=
  ∀ q, Matches T R q

/-- `T` is a distinct rival to `R`: it deviates from `R` on some question. -/
def DistinctRival {Q : Type} (T R : AnswerMap Q) : Prop :=
  ∃ q, ¬ Matches T R q

/-- `T` is committed, at `q`, to its answer: it answers `q`, and its answer
holds by its lights. -/
def CommittedAt {Q : Type} (T : AnswerMap Q) (q : Q) : Prop :=
  T.answers q ∧ T.says q

/-- The collapse lemma: a theory that mimics another on every shared question
is not a distinct rival, and it is committed at every question to whatever the
other is committed to there, the grounding question included. -/
def MimicCollapses : Prop :=
  ∀ (Q : Type) (T R : AnswerMap Q), Mimics T R →
    (∀ q, CommittedAt R q → CommittedAt T q) ∧ ¬ DistinctRival T R

end TruthCore.Metaethics

namespace TruthCore.Metaethics

/-- Regression: differing unused contents do not distinguish two unanswered maps. -/
example : Matches
    (⟨fun _ : Unit => False, fun _ => True⟩ : AnswerMap Unit)
    (⟨fun _ : Unit => False, fun _ => False⟩ : AnswerMap Unit) () :=
  ⟨Iff.rfl, fun hAnswered => hAnswered.elim⟩

/-- Regression: differing contents still distinguish answered questions. -/
example : ¬ Matches
    (⟨fun _ : Unit => True, fun _ => True⟩ : AnswerMap Unit)
    (⟨fun _ : Unit => True, fun _ => False⟩ : AnswerMap Unit) () :=
  fun h => (h.2 trivial).mp trivial

/-- Regression: answering a question differs from leaving it unexplained. -/
example : ¬ Matches
    (⟨fun _ : Unit => True, fun _ => True⟩ : AnswerMap Unit)
    (⟨fun _ : Unit => False, fun _ => True⟩ : AnswerMap Unit) () :=
  fun h => h.1.mp trivial

end TruthCore.Metaethics
