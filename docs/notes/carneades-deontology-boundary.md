# Carneades: the future-ability repair and its compatibility condition

Read the complete English `en-orig` auto-caption recording of Carneades.org,
[The Paradox of Kant's Law (Ought Implies Can)](https://www.youtube.com/watch?v=qjNs4t4GQ2A),
5:50, on 2026-10-28. Channel metadata identifies Carneades.org, not a verified
individual speaker. This is a provisional reading: audio/slides were not checked.
No attributed corpus claim or passage manifest is created. Before attribution,
obtain a producer-pinned `media_span` export, materialize it and check decisive
wording against audio. The downloaded VTT SHA256
`9aa5616c1d78e6db0007e08032e2482d240b0c5cd33634af329d4a24b1bf4ada`
identifies consulted bytes only; it is not a verified source-span hash. Reproduce:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-deontology.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=qjNs4t4GQ2A'
```

## Argument read and strongest rival

- **00:18–00:41:** presents “ought implies can.” The historical label “Kant's
  law” is the narrator's; no historical Kant attribution is authenticated here.
- **00:42–01:54:** borrowed-car return is owed, yet after a crash cannot be
  performed; debt without funds is a parallel. Retaining duty plus present
  inability conflicts with the present-ability reading. The narrator favors
  retaining the duty. This is a substantive moral commitment, not established
  by the scenario's description.
- **01:54–03:32:** proposes broad logical possibility, then objects that ability
  in a richer or more powerful world does not establish this agent's ability.
  The objection limits this repair's practical meaning, not logical consistency.
- **03:38–04:24:** fulfillment in the actual future is also too strong: the
  debtor may never earn sufficient funds, while the narrator retains the duty.
- **04:27–05:26:** proposes some possible future based on the agent's decisions;
  actual choice may lead elsewhere. Acknowledges that the weakening objection
  may persist, while preferring it to unrestricted alternative-world possibility.
- **05:26–05:50:** closing series announcement; no further premise supplied.

The exact candidate is a compatibility requirement between the ideal
continuations used to interpret obligation and the choice-accessible
continuations used to interpret ability. The strongest rival retains an
obligation even when every choice-accessible fulfilling future has closed.
Against that rival, merely naming a branching-future operator supplies no
argument. Another rival rejects ideal-world semantics of actual duties entirely.
Neither rival is eliminated by a frame correspondence theorem.

## Formal result, reuse, and rejected readings

`TruthCore.Modal.DeonticFutureBoundary` reuses canonical `Modal.Frame`; no
additional modal engine or dependency is introduced. Existing
`TemporalHistory.History` separates world, being and time and is intentionally
not reused as an agency vocabulary: it models presence-at-times, not choice.
`Modal.Holds` provides the same universal/existential shape for box/diamond;
small named predicates on continuation profiles avoid inventing a second syntax.
The new `compatibility` theorem is constructive and axiom-free: for all goal
predicates, ideal-universal obligation implies available-existential fulfillment
iff some successor is both ideal and available. Forward: instantiate the goal
with ideal accessibility itself. Backward: use a common successor for any goal.
Serial ideal accessibility alone does not establish that overlap.

The certificate adds two finite controls. First, true is the only ideal
successor, false is the only feasible successor, and both are broadly possible:
obligation and broad possibility hold, but feasible fulfillment fails. Second,
when both Boolean successors are treated as available alternative continuations,
the correspondence holds, while selecting only false as the actual continuation
still fails fulfillment. These are separate relation interpretations over complete
continuation profiles, not time instants; no temporal order, transition law,
empirical agency or metaphysical realizability is inferred. The same relation
shape can serve different controls without equating their intended meanings.

Rejected: deriving actual moral duty from an ideal frame; treating broad
possibility as ability; treating some feasible fulfilling future as actual
fulfillment; treating permission as ability; inferring present ability from
future ability; attributing the analyst's semantics to Kant; identifying return
of a destroyed original object with replacement, compensation or debt repayment.
The video's move from car-return to replacement requires a distinct action
specification. Retained responsibility for causing inability is also distinct
from an unperformable present duty. No theorem decides these moral questions.

All moral axioms and their ideal-world/agency interpretation remain open. The
certificate proves a semantic constraint and controls, not the narrator's moral
premises. It connects no Catholic-case root path and discharges no existing open
premise: intended and actual root delta zero. The attempt and dossier target
`STMT-DEONTIC-FUTURE-BOUNDARY`; no new philosophical claim is used merely to log
research activity.
