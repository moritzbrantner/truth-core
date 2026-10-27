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

`materialize` regenerates the span from a youtube-corpus `source-span` export and rejects a missing or mismatched producer revision, hash mismatch, or segment-count mismatch. The export must record exactly the passage’s pinned `producer_revision`; matching transcript text alone does not verify exporter provenance. It reads, in order, an explicit `--export FILE`, the cached whole-corpus export at `.cache/truth-core/media/source-span.json`, or a fresh export made with the checkout named by `YOUTUBE_CORPUS_DIR` (its release binary, its `git rev-parse HEAD` as producer revision, and `DATABASE_URL`). The same revision check applies to explicit, cached and freshly generated exports; an invalid export fails without falling back to another export. The materialized text lists each segment with its timestamps.

```bash
youtube-corpus ingest --url "https://www.youtube.com/watch?v=<id>" --no-asr --migrate
YOUTUBE_CORPUS_DIR=../youtube-corpus DATABASE_URL=postgres://... \
  python3 scripts/source_evidence.py materialize <PASSAGE-ID>
```

The offline `check` validates media-span manifests and claim bindings without network access. `verify` never contacts YouTube: it re-verifies media spans only when a local export is present (cached, or given with `--export`), enforcing the same revision and span checks, and otherwise lists them as not re-verified. CI therefore checks media-span structure and runs the synthetic-export tests in `scripts/test_source_evidence.py`, but cannot re-hash recordings.

Fidelity for recorded speech adds two questions to the usual ones. Auto captions can mishear words, so a claim notes its transcript source and whether the wording was checked against the audio. Speaker attribution is a judgment unless youtube-corpus speaker data confirms it; diarization labels are not identities, so a claim records how its speaker was attributed.

## Web snapshots (translations and web-only texts)

Where no git-hosted witness exists, a web page can be pinned as a passage of kind `web_snapshot` (owner decision on #154). It is the last admissible byte-pinned source kind (invariant 18); a copyrighted work with no pinnable witness falls back to a [bibliographic span](#bibliographic-spans-copyrighted-works-without-a-pinnable-witness). Its main use is a translation until a pinned Latin witness exists, such as New Advent's Summa or the isidore.co translations of Aquinas, and a web-only original such as the Latin of *Dei Filius* on vatican.va.

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

Pages change: a footer year, an analytics script, or a site edit makes the live bytes drift. Every web snapshot should therefore carry a Wayback fallback. Use a fixed-timestamp `id_` capture whose extracted text matches the pinned `text_sha256` for **every** passage of the manifest (`web-hashes … --wayback` prints `wayback_text_matches`). Fetch it twice so that `wayback_sha256` is byte-stable. If no existing capture matches but the live page still gives the pinned bytes, ask the Wayback Machine to save the page now (`https://web.archive.org/save/<URL>`), then pin the new capture after the same checks. Adding a fallback leaves `sha256`, `text_sha256` and `retrieved_at` unchanged; the `license` note says which capture was pinned and why. When no matching capture can be pinned, the note says so, and the snapshot stays fragile.

A page that drifts without a matching capture can no longer be materialized. Do not just swap in the new hashes. First compare the newly extracted text with the pinned `text_sha256`. If the text is unchanged, only the byte hash is re-pinned, and the note records the old hash and the date. If the text changed, re-read every claim on the passage against the new text before re-pinning (a fidelity review, not a hash update).

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

## Bibliographic spans (copyrighted works without a pinnable witness)

Copyrighted modern works (for example Plantinga, Flew, Ross, Pruss, van Inwagen, Ayer, or historical-Jesus scholarship) may be cited by edition and page **without pinned bytes**, but only when no pinnable witness exists: no git text, no public-domain edition, and no legitimately hosted copy that a `web_snapshot` could pin (owner decision 1c on #378). This is the passage kind `bibliographic_span`. The source record keeps its ordinary kind (`primary_text`); only the passage says how its evidence is held.

- Each passage (or its shared snapshot) gives `author`, `title`, `year` (the cited edition's publication year, an integer), a `publisher` for a book or a `journal` for an article, an `isbn` (valid ISBN-10 or ISBN-13) or a `doi` (`10.<registrant>/<suffix>`), optionally `edition`, the `language`, and an exact `pages` or `section` locator. A translated edition adds `translation` as for web snapshots, and its claims carry `basis: translation`.
- `why_bibliographic` (required) says why no pinnable witness exists: for example the copyright term, and that no legitimately hosted copy was found.
- At most a short `quotation` (about two sentences, at most 300 characters) may be committed; otherwise claims paraphrase. No text and no byte hash (`text`, `sha256`, `text_sha256`, `git_blob_sha`) is allowed on the passage.
- The conventional locator names the edition and pages, for example `Language, Truth and Logic (2nd ed. 1946), ch. 6, pp. 102-103`.

**Precedence.** `check` rejects a bibliographic span whose claim-locator prefixes overlap those of a pinned text witness or web snapshot of the same source: where the bytes can be pinned, cite them.

**Integrity marking.** Every claim on a bibliographic span carries `"witness": "bibliographic"`, and `check` rejects the field on any other claim. The marking is shown next to the claim by `corpus.py frontier` (`bibliographic witness, not byte-verified: …`), in the premise dossier, and on the explorer's claim and dossier pages, so a reader can tell verified bytes from a bibliographic reference.

**Verification.** `check` validates the record and its claim bindings. `verify` fetches nothing for it and lists it as `bibliographic spans not byte-verified`. `materialize` refuses it: there are no bytes to extract. A worker therefore claims from a bibliographic span only after reading the cited pages in the edition itself (for example the owner's copy), never from memory or a search snippet (invariant 2). Source integrity for such a claim rests on the citation and the reader's checking, not on a hash; source fidelity remains a review question as everywhere.

### Upgrade path

A bibliographic span is a placeholder for pinned evidence. When a pinnable witness appears (a `web_snapshot` of a legitimately hosted copy, a public-domain edition in git, or an owner-held local copy pinned by hash under the future option 1b), replace the passage in place:

1. Add the pinned passage with the **same source ID and claim-locator prefixes** (a manifest of the new kind; the old `bibliographic_span` entry is removed in the same change, since `check` rejects an overlap). Claims bind by source ID and locator, so their IDs and locators stay unchanged.
2. Materialize the new witness and re-read every claim on the passage against the verified text. A reading that no longer holds is revised as a new claim, as for any fidelity review.
3. Remove `"witness": "bibliographic"` from those claims (`check` rejects it on a pinned witness).

Option 1b (owner-held copies pinned by hash) is not implemented yet; it would need a passage kind that pins a local file's hash without committing its bytes.

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

`verify` also refetches every web snapshot, live or from its Wayback capture, and checks bytes and extracted text. `verify --base <REF> [--head <REF>]` refetches only the passages whose manifest files changed between the two commits. It refetches all of them when `scripts/source_evidence.py` itself changed. Every manifest and claim binding is still validated offline.

CI runs the corpus binding check on every run. On a pull request it runs `verify --base HEAD^1 --head HEAD`, so each passage the PR adds or changes is fetched and checked. Unrelated PRs are no longer blocked by a page that drifted outside the repository. On a push to `main`, and in the nightly scheduled run, CI runs the full `verify`. Drift therefore still turns `main` and the nightly run red, where the owner is notified. The repair is a fallback or re-pin as described above. New claims therefore cannot enter the formalized corpus without reproducible source evidence, except claims on a bibliographic span, which are marked `witness: "bibliographic"` and listed as not byte-verified.

## What this does not prove

The source-evidence layer intentionally does not use an LLM score as a truth oracle. It cannot mechanically establish that:

- a paraphrase captures every relevant nuance;
- a chosen formalization has the correct quantifier scope, modality, identity conditions, causal semantics, or historical intent;
- one defensible interpretation is uniquely correct; or
- the philosophical premise itself is true.

Those are handled by explicit interpretation notes, fidelity critique, alternative claims, and human or scholarly review. The source-evidence layer makes that review auditable because the underlying witness is stable and reproducible.
