namespace TruthCore.Causality

/-- A static Grim Reaper schedule. Index `n + 1` denotes a Reaper whose
deadline is earlier than index `n`'s. Reaper `n` acts if and only if no
earlier-deadline Reaper acts. This is a *stipulated* law, not a consequence
of there being infinitely many ordered causes. -/
def GrimReaperLaw (acts : Nat → Prop) : Prop :=
  ∀ n, acts n ↔ ∀ m, n < m → ¬ acts m

/-- A finite schedule uses the same law, but only among its finitely many
Reapers. A last index (first deadline) is then available. -/
def FiniteGrimReaperLaw {size : Nat} (acts : Fin size → Prop) : Prop :=
  ∀ n, acts n ↔ ∀ m, n < m → ¬ acts m

/-- The impossibility claim is about this *particular* stipulated rule. -/
def NoFirstGrimReaperSchedule : Prop :=
  ¬ ∃ acts : Nat → Prop, GrimReaperLaw acts

/-- A finite version of the stipulated action rule is satisfiable. -/
def ConsistentFiniteThreeReapers : Prop :=
  ∃ acts : Fin 3 → Prop, FiniteGrimReaperLaw acts

end TruthCore.Causality
