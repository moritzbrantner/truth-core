import TruthCore.German.Wittgenstein.OnCertainty
namespace TruthCore.Results.Wittgenstein.DoubtPresupposesCertainty
open TruthCore.German.Wittgenstein.OnCertainty

/-- *Über Gewißheit* §115 from §341: if every doubt rests on some sentence
exempt from doubt, then whoever doubted everything would not get as far as
doubting. The universal doubter's own doubt supplies an exempt sentence, which
the universality of the doubt denies. -/
theorem universalDoubtFails {Sentence : Type} (Doubted : Sentence → Prop)
    (hRests : DoubtRestsOnExemptionReading Doubted) :
    UniversalDoubtFails Doubted := by
  intro ⟨⟨s, hDoubted⟩, hAll⟩
  obtain ⟨h, hExempt⟩ := hRests s hDoubted
  exact hExempt (hAll h)

/-- The §341 premise is needed: a one-sentence language in which that sentence
is doubted satisfies universal doubt. -/
theorem needsDoubtRestsOnExemption :
    ¬ ∀ (Sentence : Type) (Doubted : Sentence → Prop), UniversalDoubtFails Doubted := by
  intro h
  exact h Unit (fun _ => True) ⟨⟨(), trivial⟩, fun _ => trivial⟩

/-- What the premise does not give: it is consistent with doubting any one
chosen sentence. In a two-sentence language where the first is doubted and the
second exempt, §341 holds and the first is doubted. So the argument picks out no
particular hinge, such as "something changes" or "something is moved". -/
theorem anyGivenSentenceDoubtable :
    ∃ (Doubted : Bool → Prop), DoubtRestsOnExemptionReading Doubted ∧ Doubted true := by
  refine ⟨fun b => b = true, fun _ _ => ⟨false, Bool.false_ne_true⟩, rfl⟩

end TruthCore.Results.Wittgenstein.DoubtPresupposesCertainty
