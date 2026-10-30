import Mathlib.Logic.Function.Basic

namespace TruthCore.Epistemology.FitnessTruthBoundary

/-- Analyst's binary response rule: `false` polarity follows a represented binary
state; `true` polarity reverses it. Polarity is a deliberately thin proxy for
an action preference, not a complete desire psychology. Motivated by Plantinga,
WCB III.7.IV.B, teaching excerpt p.10 (pinned passage
PLANTINGA-WCB-EAAN-BEHAVIOR-DESIRE); the XOR rule is not attributed to him. -/
def act (belief polarity : Bool) : Bool := if polarity then !belief else belief

/-- Every response matches its supplied target. No evolutionary dynamics or
probability measure is encoded by this exact behavioral-success condition. -/
def Successful {S : Type} (target belief polarity : S → Bool) : Prop :=
  ∀ s, act (belief s) (polarity s) = target s

/-- Exact truth at every state in this binary representation; stronger than
probabilistic or approximate cognitive reliability. -/
def Truthful {S : Type} (target belief : S → Bool) : Prop := ∀ s, belief s = target s

/-- Following, rather than reversing, represented states at every input. This
is a bridge condition for this rule, not an empirical assumption about desire. -/
def Direct {S : Type} (polarity : S → Bool) : Prop := ∀ s, polarity s = false

/-- Pointwise exact compensation, universal response controls, and two inhabited
opposite-truth profiles with the same fully successful responses. The final
clause shows that any behavioral score assigns those response functions equal
scores; it says nothing about the probability of either cognitive profile. -/
def Certificate : Prop :=
  (∀ b d t : Bool, act b d = t ↔ d = Bool.xor b t) ∧
  (∀ (S : Type) (t b : S → Bool), ∃ d, Successful t b d) ∧
  (∀ (S : Type) (t b d : S → Bool), Successful t b d →
    (Truthful t b ↔ Direct d)) ∧
  (∃ (bt dt bf df : Bool → Bool),
    Successful id bt dt ∧ Successful id bf df ∧ Truthful id bt ∧
    (∀ s, bf s ≠ s) ∧ ¬ Truthful id bf ∧
    (∀ s, act (bt s) (dt s) = act (bf s) (df s)) ∧
    (∀ score : (Bool → Bool) → Nat,
      score (fun s => act (bt s) (dt s)) = score (fun s => act (bf s) (df s))))

end TruthCore.Epistemology.FitnessTruthBoundary
