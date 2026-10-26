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

CTS edition URNs must extend the source's work URN. Works without CTS identifiers (for example Aquinas via SCTA resource URIs) instead list each admitted edition identifier in the source record's `edition_urns`, kept sorted (`corpus.py check` requires it, and `python3 scripts/corpus.py sort-lists` sorts it) so that concurrent additions do not all conflict at the end of the list. Materialization joins words across TEI `<lb break="no"/>` line breaks.

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

## Web snapshots (translations and web-only texts)

Where no git-hosted witness exists, a web page can be pinned as a passage of kind `web_snapshot` (owner decision on #154). It is the last admissible source kind (invariant 18). Its main use is a translation until a pinned Latin witness exists, such as New Advent's Summa or the isidore.co translations of Aquinas, and a web-only original such as the Latin of *Dei Filius* on vatican.va.

- The manifest's **snapshot** (`kind: "web_snapshot"`) names the `source_url`, the `retrieved_at` UTC timestamp, the `sha256` of the response bytes (after removing any gzip content coding), the page `encoding`, the `language`, and in `license` the terms or copyright notice found on the site. A translation adds `translation` with `translator`, `year` and `edition`. An optional `wayback_url` of the form `https://web.archive.org/web/<14-digit timestamp>id_/<source_url>` gives a fixed-timestamp capture, with its own `wayback_sha256`.
- Each **passage** gives an `html_selector`, the `text_sha256` of the extracted text, and optionally an `incipit` of at most 80 characters. The selector is one of `{"element_id": ...}` (that element; one whose end tag may be omitted, such as `p`, `li`, `dt`/`dd` or a table row or cell, ends where HTML implies its end: at the next start tag that closes it or at the end of its parent), `{"heading": ...}` (an `h1`–`h6` with exactly that text, up to the next heading of the same or a higher level), or `{"from": marker, "to": marker}` with `to` optional and excluded, where a marker is `{"anchor": ...}` (a tag with that `name` or `id`) or `{"text": ...}` (a block whose whole text is exactly that). Every selector must match exactly once.
- Plain-text source files with an immutable URL may instead set `"raw_text": true` on the passage. This bypasses HTML parsing, retains line breaks and source syntax, and strips only leading/trailing whitespace; it is suitable for a hash-pinned `.thy` file. Exactly one of `html_selector`, `pdf_pages` and `raw_text` is permitted. This is a byte/text extraction variant of the existing `web_snapshot` kind, not a new source kind.
- **No page text is committed**, only hashes, locators and a short incipit, so copyrighted translations can be cited. `check` rejects a web-snapshot passage carrying `text`.

`materialize` fetches the page with a fixed User-Agent and rejects byte drift. If the live page drifted or is unreachable, it fetches the Wayback capture and checks it against `wayback_sha256`. It then extracts the selected range, normalizes it to one line per HTML block, and rejects a `text_sha256` mismatch, which also catches a changed extractor or selector. Verified bytes are cached under `.cache/truth-core/web/` by hash, so a later `materialize` works offline. The Wayback capture is only a fallback: its bytes may differ from the live page (for example by injected scripts) as long as the extracted text matches. `verify` refetches every web snapshot without the cache. The offline `check` validates the manifests and claim bindings only.

To pin a new page, fetch it twice to make sure it is byte-stable, then print the fields with:

```bash
python3 scripts/source_evidence.py web-hashes <URL> --encoding utf-8 \
  --selector '{"from": {"anchor": "13"}, "to": {"anchor": "14"}}' \
  --wayback 'https://web.archive.org/web/<timestamp>id_/<URL>'
```

Pages change: a footer year, an analytics script, or a site edit makes the live bytes drift. Record a Wayback capture whose extracted text matches whenever one is reachable. A page that drifts without a matching capture can no longer be materialized; re-pin it, and re-read the claims against the new text.

### PDF pages within a web snapshot

A primary PDF uses the same `web_snapshot` kind and byte/text hashes. In place
of `html_selector`, set `pdf_pages: {"first": 2, "last": 10}` with inclusive,
one-based physical PDF pages; the conventional locator separately records the
printed pagination. Exactly one selector is required. Materialization invokes
Poppler's `pdftotext` with UTF-8 output and a 30-second limit, normalizes all
whitespace to single spaces, and checks `text_sha256`. Changes in extraction
therefore fail rather than silently changing the consulted text. Empty or
image-only extraction is rejected; this adapter does not perform OCR.

Install Poppler (`sudo apt-get install poppler-utils` on Debian/Ubuntu).
`web-hashes URL --encoding utf-8 --pdf-pages FIRST:LAST` prints pinning fields.
Fetch twice and inspect the verified materialization before source claims,
just as for HTML. Copyrighted PDFs and their extracted text stay in ignored
local caches; only hashes, locators, terms and short incipits are committed.

For an immutable plain-text file, use `web-hashes URL --encoding utf-8 --raw-text`.
For example, the AFP `GoedelGod.thy` witness now uses an official Git mirror's
commit-pinned raw URL instead of the AFP's release-dependent HTML presentation.
Its file SHA-256 is cross-checked against the historical AFP release tarball.

### Translation basis

A translation is not the primary text. Every claim on a passage with `translation` must carry `"basis": "translation"`, and `basis` is rejected on any other claim. A translation-based claim stays a candidate for upgrade to a pinned Latin witness, and it may not override a reading of one. `check` enforces two rules for this:

- a web snapshot may not cover a range that a pinned git text witness of the same source covers (no claim-locator prefix of one may be a prefix of the other's); once the Latin is pinned, its claims move to the Latin witness;
- a translation-based claim may not be an `interpretation_of` (an alternative reading of) a claim read from an original-language witness.

Whether a translation-based claim conflicts in meaning with a Latin-based claim on another statement remains a review question.

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

Media spans and web snapshots follow their own steps (see above) and write their text to the same place.

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

`verify` also refetches every web snapshot, live or from its Wayback capture, and checks bytes and extracted text. CI runs the corpus binding check and verifies the immutable source snapshots. New claims therefore cannot enter the formalized corpus without reproducible source evidence.

## What this does not prove

The source-evidence layer intentionally does not use an LLM score as a truth oracle. It cannot mechanically establish that:

- a paraphrase captures every relevant nuance;
- a chosen formalization has the correct quantifier scope, modality, identity conditions, causal semantics, or historical intent;
- one defensible interpretation is uniquely correct; or
- the philosophical premise itself is true.

Those are handled by explicit interpretation notes, fidelity critique, alternative claims, and human or scholarly review. The source-evidence layer makes that review auditable because the underlying witness is stable and reproducible.
