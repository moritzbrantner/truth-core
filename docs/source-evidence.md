# Source evidence

`truth-core` keeps source integrity, source fidelity, and formal verification separate.

## Three verification boundaries

1. **Source integrity** asks which primary-source bytes were consulted. This is reproducible and mechanically checkable.
2. **Source fidelity** asks whether a claim is a defensible interpretation of those bytes in context. This remains scholarly review and may admit multiple readings.
3. **Formal verification** asks whether a Lean conclusion follows from the advertised formal premises. Lean, NanoDa, and Comparator operate here.

A green result in one layer never implies that the later layers are green. In particular, a hash-verified Aristotle witness does not prove that Aristotle meant a claim, and a Comparator proof does not establish source fidelity.

## Source and passage records

`corpus/sources/` identifies works and their conventional citation systems. `corpus/passages/` identifies reproducible evidence ranges inside immutable digital editions.

Each passage manifest has two parts:

- a **snapshot**, shared by one or more passage ranges, containing the source ID, exact edition URN, language, public repository, immutable revision SHA, file path, Git blob SHA, immutable raw URL, and license;
- one or more **passages**, containing a stable passage ID, conventional human locator, claim-locator prefixes, and an optional extraction selector: a CTS path (`cts_path`) or, for TEI witnesses without CTS structure, the unique `xml:id` of the range's element (`tei_xml_id`).

CTS edition URNs must extend the source's work URN. Works without CTS identifiers (for example Aquinas via SCTA resource URIs) instead list each admitted edition identifier in the source record's `edition_urns`. Materialization joins words across TEI `<lb break="no"/>` line breaks.

The conventional locator remains the citation scholars should read, such as `Physics I.4, 187b7-13` or `Timaeus 28a`. The pinned digital witness answers the different question: exactly which edition bytes did the worker inspect?

## Media spans (recorded speech)

Recorded debates and lectures are admissible sources of arguments (owner decision on #152). They use the source kind `media_recording` and the passage kind `media_span`, cited through [youtube-corpus](https://github.com/moritzbrantner/youtube-corpus) transcripts.

- The **source** record (`kind: "media_recording"`) names the recording: `youtube_id`, title (`work`), `channel`, `upload_date`, and the YouTube URL as `work_urn` and `catalog_url`.
- The **passage** manifest's snapshot (`kind: "media_span"`) names the `youtube_id`, the `transcript_source` (`caption_manual`, `caption_auto` or `asr`), the `language`, the `producer` (`youtube-corpus`) with its `producer_revision` (`git:<sha>`), and the export schema `source_span_interchange@1`. Each passage gives `start_seconds`, `end_seconds`, the `segment_count`, a `span_sha256`, and optionally the `speaker` with a `speaker_attribution` note.
- The conventional locator is `<speaker>, "<title>" (<channel>, <upload date>), mm:ss–mm:ss`.
- **No transcript text is committed.** `check` rejects a media-span passage carrying `text` or `transcript`.

The span hash covers the transcript segments of the pinned stream whose interval overlaps `[start_seconds, end_seconds)`, in time order: the SHA-256 of the canonical JSON list of each segment's `segmentIndex`, `startSeconds`, `endSeconds` and the SHA-256 of its text. Database ids are left out because they differ between ingests. A changed caption, a re-segmentation, or a timing shift changes the hash.

`materialize` regenerates the span from a youtube-corpus `source-span` export and rejects a hash or segment-count mismatch. It reads, in order, an explicit `--export FILE`, the cached whole-corpus export at `.cache/truth-core/media/source-span.json`, or a fresh export made with the checkout named by `YOUTUBE_CORPUS_DIR` (its release binary, its `git rev-parse HEAD` as producer revision, and `DATABASE_URL`). The materialized text lists each segment with its timestamps.

```bash
youtube-corpus ingest --url "https://www.youtube.com/watch?v=<id>" --no-asr --migrate
YOUTUBE_CORPUS_DIR=../youtube-corpus DATABASE_URL=postgres://... \
  python3 scripts/source_evidence.py materialize <PASSAGE-ID>
```

The offline `check` validates media-span manifests and claim bindings without network access. `verify` never contacts YouTube: it re-verifies media spans only when a local export is present (cached, or given with `--export`) and otherwise lists them as not re-verified. CI therefore checks media-span structure and runs the synthetic-export tests in `scripts/test_source_evidence.py`, but cannot re-hash recordings.

Fidelity for recorded speech adds two questions to the usual ones. Auto captions can mishear words, so a claim notes its transcript source and whether the wording was checked against the audio. Speaker attribution is a judgment unless youtube-corpus speaker data confirms it; diarization labels are not identities, so a claim records how its speaker was attributed.

## Claim binding

Claims deliberately remain small. A formalized claim records its source ID and precise locator. `scripts/source_evidence.py` requires that pair to resolve to exactly one passage witness.

This keeps proposition identity independent of provenance while making provenance mandatory. Adding a plausible locator to a valid source ID is no longer enough for a claim to pass corpus validation.

## Worker workflow

Before a worker interprets a candidate range:

```bash
python3 scripts/source_evidence.py materialize ARIST-PHYS-I-4
```

The command:

1. resolves the passage manifest;
2. downloads the source file from its immutable revision;
3. recomputes the Git blob SHA and rejects any mismatch;
4. parses the source XML;
5. extracts the configured CTS range when one is available; and
6. writes normalized UTF-8 text under `.cache/truth-core/sources/`.

Workers must read that materialized text and relevant context before creating claims. Model memory, search-result snippets, or an unpinned web page are orientation aids only.

## Validation

Offline structural validation:

```bash
python3 scripts/source_evidence.py check
python3 scripts/corpus.py check
```

Network-backed source verification:

```bash
python3 scripts/source_evidence.py verify
```

CI runs the corpus binding check and verifies the immutable source snapshots. New claims therefore cannot enter the formalized corpus without reproducible source evidence.

## What this does not prove

The source-evidence layer intentionally does not use an LLM score as a truth oracle. It cannot mechanically establish that:

- a paraphrase captures every relevant nuance;
- a chosen formalization has the correct quantifier scope, modality, identity conditions, causal semantics, or historical intent;
- one defensible interpretation is uniquely correct; or
- the philosophical premise itself is true.

Those are handled by explicit interpretation notes, fidelity critique, alternative claims, and human or scholarly review. The source-evidence layer makes that review auditable because the underlying witness is stable and reproducible.
