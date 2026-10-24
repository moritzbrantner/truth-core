import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., the *quarta via*: things are found more and less true;
more and less are said by approach to a maximum, so something is maximally true;
the maximally true is maximally being; and the maximum in a genus causes all in
that genus. So something maximal in being causes the being of every other being. -/
theorem quartaVia {Being : Type} {Respect : Type}
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (bonum verum nobile esse : Respect)
    (hGrades : GradesFoundInThingsReading MoreIn bonum verum nobile)
    (hApproach : GradesByApproachToAMaximumReading InAct MoreIn)
    (hTrue : MostTrueIsMostBeingReading InAct MoreIn verum esse)
    (hGenus : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn) :
    MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  -- INF-AQUINAS-ST-I-Q2-A3-QUARTA-VIA: grades of truth have a maximum,
  obtain ⟨_, hVerum, _⟩ := hGrades
  obtain ⟨m, hMaxVerum⟩ := hApproach verum hVerum
  -- which is maximal in being,
  have hMaxEsse : IsMaximumIn InAct MoreIn esse m := hTrue m hMaxVerum
  -- and so, by the genus principle at esse, causes the being of all others
  have hCauses : CausesAllInGenus InAct CausesIn esse m := hGenus esse m hMaxEsse
  exact ⟨m, hMaxEsse, hCauses⟩

/-- The maximum premise is needed. On the natural numbers ordered by size, with
one perfection that everything has, there are grades but no maximum: the other
three premises hold (vacuously) and the conclusion fails. -/
theorem quartaViaNeedsMaximum :
    ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (bonum verum nobile esse : Respect),
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn →
      MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse := by
  intro h
  have noMax : ∀ (m : Nat), ¬ IsMaximumIn (fun (_ : Nat) (_ : Unit) => True)
      (fun _ y x => x < y) () m :=
    fun m hm => hm.2 (m + 1) (Nat.lt_succ_self m)
  obtain ⟨m, hm, _⟩ := h Nat Unit (fun _ _ => True) (fun _ y x => x < y)
    (fun _ _ _ => False) () () () ()
    ⟨⟨1, 0, Nat.zero_lt_one⟩, ⟨1, 0, Nat.zero_lt_one⟩, ⟨1, 0, Nat.zero_lt_one⟩⟩
    (fun m hm => absurd hm (noMax m))
    (fun _ m hm => absurd hm (noMax m))
  exact noMax m hm
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaVia
