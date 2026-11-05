module

public import TruthCore.Logic.Verificationism

/-!
A concrete language for the verificationism results (#1008): individuals
`0, 1, 2, …`, atomic sentences `r n` ("n is a raven") and `b n` ("n is black"),
the universal law "every raven is black", and the Boolean connectives. Worlds
assign each individual its two atomic values. The observation statements are
the quantifier-free sentences; each is about the individuals it names.

The model shows that the hypotheses of the results are satisfiable:
`ravensSetting` is a `LawSetting`, and `r 0`, `r 1`, `r 2` are observation
statements as Church's construction uses them (in the Church solution). It is
a satisfiability witness, not an account of observation.
-/
@[expose] public section

namespace TruthCore.Logic.Verificationism.Model

open TruthCore.Logic.Verificationism

/-- Sentences of a small first-order-style language over individuals `0, 1, 2, …`. -/
inductive LawSentence where
  | r (n : Nat)
  | b (n : Nat)
  | law
  | neg (s : LawSentence)
  | conj (s t : LawSentence)
  | disj (s t : LawSentence)

namespace LawSentence

def eval (w : Nat → Bool × Bool) : LawSentence → Prop
  | r n => (w n).1 = true
  | b n => (w n).2 = true
  | law => ∀ n, (w n).1 = true → (w n).2 = true
  | neg s => ¬ s.eval w
  | conj s t => s.eval w ∧ t.eval w
  | disj s t => s.eval w ∨ t.eval w

def quantifierFree : LawSentence → Prop
  | r _ => True
  | b _ => True
  | law => False
  | neg s => s.quantifierFree
  | conj s t => s.quantifierFree ∧ t.quantifierFree
  | disj s t => s.quantifierFree ∧ t.quantifierFree

def atoms : LawSentence → List Nat
  | r n => [n]
  | b n => [n]
  | law => []
  | neg s => s.atoms
  | conj s t => s.atoms ++ t.atoms
  | disj s t => s.atoms ++ t.atoms

end LawSentence

def lawLanguage : Language where
  Sentence := LawSentence
  World := Nat → Bool × Bool
  holds w s := s.eval w
  neg := .neg
  conj := .conj
  disj := .disj
  holds_neg _ _ := Iff.rfl
  holds_conj _ _ _ := Iff.rfl
  holds_disj _ _ _ := Iff.rfl

def lawFrame : Frame lawLanguage where
  observation s := LawSentence.quantifierFree s
  analytic _ := False

def ravens : UniversalLaw lawLanguage where
  Individual := Nat
  R := .r
  B := .b
  law := .law
  holds_law _ := Iff.rfl

def counterAt (w : Nat → Bool × Bool) (a : Nat) : Nat → Bool × Bool :=
  fun n => if n = a then (true, false) else w n

theorem le_sum : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr (· + ·) 0
  | [], _, h => nomatch h
  | y :: l, x, h => by
    cases h with
    | head => exact Nat.le_add_right _ _
    | tail _ h => exact Nat.le_trans (le_sum l x h) (Nat.le_add_left _ _)

theorem counterAt_preserves (w : Nat → Bool × Bool) (a : Nat) :
    ∀ o : LawSentence, o.quantifierFree → ¬ a ∈ o.atoms →
      (o.eval (counterAt w a) ↔ o.eval w)
  | .r n, _, ha => by
    have hne : ¬ n = a := fun h => ha (h ▸ List.Mem.head _)
    show ((if n = a then (true, false) else w n).1 = true) ↔ (w n).1 = true
    rw [ite_eq_right hne]
  | .b n, _, ha => by
    have hne : ¬ n = a := fun h => ha (h ▸ List.Mem.head _)
    show ((if n = a then (true, false) else w n).2 = true) ↔ (w n).2 = true
    rw [ite_eq_right hne]
  | .law, hq, _ => nomatch hq
  | .neg s, hq, ha => by
    have ih := counterAt_preserves w a s hq ha
    exact ⟨fun h h' => h (ih.mpr h'), fun h h' => h (ih.mp h')⟩
  | .conj s t, hq, ha => by
    have ihs := counterAt_preserves w a s hq.1 (fun h => ha (List.mem_append_left _ h))
    have iht := counterAt_preserves w a t hq.2 (fun h => ha (List.mem_append_right _ h))
    exact ⟨fun h => ⟨ihs.mp h.1, iht.mp h.2⟩, fun h => ⟨ihs.mpr h.1, iht.mpr h.2⟩⟩
  | .disj s t, hq, ha => by
    have ihs := counterAt_preserves w a s hq.1 (fun h => ha (List.mem_append_left _ h))
    have iht := counterAt_preserves w a t hq.2 (fun h => ha (List.mem_append_right _ h))
    exact ⟨fun h => h.elim (fun h => Or.inl (ihs.mp h)) (fun h => Or.inr (iht.mp h)),
      fun h => h.elim (fun h => Or.inl (ihs.mpr h)) (fun h => Or.inr (iht.mpr h))⟩

def ravensSetting : LawSetting lawFrame ravens where
  mentions o a := a ∈ LawSentence.atoms o
  finite_mentions o _ := ⟨o.atoms, fun _ h => h⟩
  infinite (l : List Nat) := ⟨l.foldr (· + ·) 0 + 1, fun h => Nat.not_succ_le_self _ (le_sum l _ h)⟩
  vary w (a : Nat) := ⟨counterAt w a,
    by show ((if a = a then (true, false) else w a).1 = true); rw [ite_eq_left rfl],
    by show ¬ ((if a = a then (true, false) else w a).2 = true); rw [ite_eq_left rfl]; exact Bool.noConfusion,
    fun o ho hm => counterAt_preserves w a o ho hm⟩

/-- World at which only individual `k` is a black raven. -/
def oneAt (k : Nat) : Nat → Bool × Bool := fun n => if n = k then (true, true) else (false, false)

end TruthCore.Logic.Verificationism.Model
