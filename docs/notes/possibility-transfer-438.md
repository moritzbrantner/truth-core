# Two-relation possibility control (#438)

The missing bridge is now explicit: for every carrier D, pair of frames E/M
and origin w, `(∀ P, Dia E P w → Dia M P w) ↔ IncludedAt E M w`.
The box direction is `(∀ P, Box M P w → Box E P w) ↔ IncludedAt E M w`.
`diamond_transfer_iff` tests singleton predicates for necessity;
`box_transfer_iff` tests the M-successor predicate. Sufficiency transports
accessibility. These are constructive consequences, not transcriptions of an
assumed bridge. Full predicate quantification matters; no claim is made for a
restricted language without separating predicates.

The omitted-inclusion control uses two candidate descriptions (Bool), universal
E, identity M, origin false, and P(v) := v = true. Both frames are reflexive,
symmetric and transitive. P has a satisfying description and an E-witness, but
no M-witness at false. M-box-not-P holds and E-box-not-P fails. This is a
nonempty-accessibility control. It does not call the excluded candidate a
genuinely metaphysically possible world, or turn semantic satisfiability into
syntactic consistency. No theorem interprets absence of a proof as possibility.
Logical, conceptual and nomological possibility are not identified with these
stipulated E/M profiles.

Reuse: `TruthCore.Modal.Frame`, the existing `GoedelGod.MProp/Box/Dia`, and
`Models.FiniteSupport`. The #248 `Conceivability.StrongBridge` instead has an
arbitrary conception operator; its theorem does not characterize two-relation
inclusion. The #262–268 research controls concern individual modal frame
conditions, collapse, extensionality and propagation, not this cross-relation
bridge. No geometry, modal-duality, or collapse matrix was repeated. No Hume
claim was added; its source-specific conception and withholding reading remain
separate. Existing dossier `STMT-HUME-CONCEIVABILITY-TESTS` was inspected.

Premise comparison: no premises retained, added, removed or discharged at the
corpus argument boundary. The closed theorem quantifies over profiles and
contains conditional laws; it does not establish inclusion for actual knowledge
or metaphysical possibility. Root-path open-premise change is exactly zero.
Actual epistemic adequacy and metaphysical fidelity remain open research
obligations. `ATTEMPT-MODAL-POSSIBILITY-TRANSFER` records the result and rejected
interpretations; the generated dossier is not an independent authority.

Challenge frozen before solution: SHA256
`cb22f876bd3f58392488f47fe43873aec5383439456f369d17321627c7c410ef`.
Self-sweep: statement, argument, result description and comments all describe
`Checks = TransferLaws ∧ OmissionControl`; no unlisted nonemptiness condition,
actual metaphysical conclusion, historical attribution or proof-search result.
All load-bearing terms link the stipulative definitions and E/M disambiguation.

Local service: coordinator workspace
`/home/brantner/privat/truth-core-sprint-proof`, preview HEAD
`49b4589aa6744c91a6bc9adec13215d0e7245c9d`, persistent session
`causal-harvest`, virtual path `Scratch/issue438/PossibilityTransfer.lean`.
The client held `flock /tmp/truth-core-lean.lock` and POSTed full concatenated
module/solution text (omitting the solution's local import) to
`http://127.0.0.1:8765/lean/diagnostics`; no preview files/imports were changed.
An initial `decide` needed explicit unfolding of the control definitions;
the corrected version had no diagnostics. A repeated edit adding `#print axioms`
reported no axioms, content SHA256
`dc58eb7310e6da45e7d55eb22b49fed6f44533181ddca983ba3c4c431a8e32f3`,
version 3. A goal lookup at line 62 returned null at that position; no goal
claim is based on it. The response reports the preview dirty state and diff
SHA256 `660a0c8ebd32fec39115624b54b7ad33ab84bc3a9f5a747f309f92e4ee27556c`.
This is interactive proof feedback, not canonical Comparator/NanoDa evidence;
final CI verifies canonical modules. Retain the service for repeated proof
edits; no CLI performance comparison was run in this lane.
