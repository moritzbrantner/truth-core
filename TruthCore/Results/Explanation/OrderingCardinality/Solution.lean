module

public import TruthCore.Explanation.OrderingCardinality

@[expose] public section

namespace TruthCore.Results.Explanation.OrderingCardinality
open Cardinal TruthCore.Explanation.OrderingCardinality
open TruthCore.Explanation.HistorySelection

/-- An omega-order has no nontrivial order automorphism. Both comparison maps
are increasing, so each is at least the identity; being inverses forces equality. -/
theorem earlier_injective : Function.Injective earlier := by
  intro e f h
  have hf : StrictMono (fun n => f.symm (e n)) := by
    intro i j hij
    have hp : earlier e (e i) (e j) := by simpa [earlier] using hij
    change earlier f (e i) (e j)
    rw [← h]
    exact hp
  have hg : StrictMono (fun n => e.symm (f n)) := by
    intro i j hij
    have hp : earlier f (f i) (f j) := by simpa [earlier] using hij
    change earlier e (f i) (f j)
    rw [h]
    exact hp
  apply Equiv.ext
  intro n
  have hle : f.symm (e n) ≤ n := by
    simpa using hg.id_le (f.symm (e n))
  have hn : f.symm (e n) = n := le_antisymm hle (hf.id_le n)
  have := congrArg f hn
  simpa using this

theorem cardinality : Cardinality := by
  have hc : #(Arrangement) = 2 ^ aleph0 := by
    simpa only [mk_nat] using (mk_perm_eq_two_power (α := Nat))
  exact ⟨hc, hc ▸ cantor aleph0, earlier_injective,
    (mk_range_eq earlier earlier_injective).trans hc⟩

/-- Induction uses the rule once as a general hypothesis; it does not inspect
infinitely many separate cases. Applicability of that rule remains a separate question. -/
theorem reconstruct (e : Arrangement) (f : Nat → Nat)
    (hz : f 0 = e 0) (hs : ∀ n, f (n + 1) = next e (f n)) :
    ∀ n, f n = e n := by
  intro n
  induction n with
  | zero => exact hz
  | succ n ih => simpa [ih, next] using hs n

theorem data_injective : Function.Injective chainData := by
  intro e f h
  have hz : e 0 = f 0 := congrArg Prod.fst h
  have hs : next e = next f := congrArg Prod.snd h
  apply Equiv.ext
  exact reconstruct f e hz (fun n => by rw [← hs]; simp [next])

theorem constant_failure (a : Arrangement) :
    ¬ ∃ p, EvidenceOnly (fun (_ : Arrangement) (_ : Unit) => True)
      (fun _ => True) p ∧ Selects a p := by
  rintro ⟨p, hp, hpa, hselect⟩
  let b : Arrangement := a.trans (Equiv.swap (a 0) (a 1))
  have hba : b ≠ a := by
    intro he
    have hz := congrArg (fun e : Arrangement => e 0) he
    have hn : a 1 = a 0 := by simpa only [b, Equiv.trans_apply, Equiv.swap_apply_left] using hz
    exact (Nat.zero_ne_one (a.injective hn.symm))
  have hb : p b := (hp b a (fun _ _ => Iff.rfl)).mpr hpa
  exact hba (hselect b hb)

theorem complete_information (a : Arrangement) :
    ∃ p, EvidenceOnly FullTruth (fun _ => True) p ∧ Selects a p := by
  refine ⟨fun e => e = a, ?_, rfl, fun _ he => he⟩
  intro e f hef
  have hd : chainData e = chainData f := by
    apply Prod.ext
    · exact (hef (e 0, none) trivial).mp rfl |>.symm
    · funext x
      exact (hef (next e x, some x) trivial).mp rfl |>.symm
  have heq := data_injective hd
  exact heq ▸ Iff.rfl

theorem controls : Controls := by
  refine ⟨data_injective, ?_, ?_, reconstruct, constant_failure, complete_information⟩
  · intro e
    refine ⟨fun x => ⟨next e x, rfl⟩, ?_⟩
    intro h
    exact h.not_rightTotal (fun x => ⟨next e x, rfl⟩)
  · constructor
    · simp only [mk_arrow, mk_bool, mk_nat, lift_id]
    · exact ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩

end TruthCore.Results.Explanation.OrderingCardinality
