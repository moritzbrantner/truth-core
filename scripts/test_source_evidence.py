"""Offline tests for media_span and web_snapshot evidence (synthetic fixtures, no network)."""

from __future__ import annotations

import contextlib
import copy
import io
import json
import tempfile
import unittest
from unittest import mock
from pathlib import Path

import source_evidence as se


def span(stream: str, index: int, start: float, end: float, text: str) -> dict:
    return {
        "id": f"span-{stream}-{index}",
        "sourceId": stream,
        "sequence": index,
        "text": text,
        "contentHash": se.sha256_text(text),
        "language": "en",
        "locator": {"kind": "timed", "segmentIndex": index, "startSeconds": start, "endSeconds": end},
    }


EXPORT = {
    "schema": "source_span_interchange",
    "schemaVersion": 1,
    "producer": {"name": "youtube-corpus", "revision": "git:fixture"},
    "sources": [
        {
            "id": "stream-auto",
            "kind": "youtube_transcript",
            "language": "en",
            "metadata": {"youtubeId": "abc123XYZ_0", "transcriptSource": "caption_auto"},
        },
        {
            "id": "stream-manual",
            "kind": "youtube_transcript",
            "language": "en",
            "metadata": {"youtubeId": "abc123XYZ_0", "transcriptSource": "caption_manual"},
        },
    ],
    "spans": [
        span("stream-auto", 0, 0.0, 4.0, "a synthetic opening line"),
        span("stream-auto", 1, 4.0, 9.5, "the synthetic claim itself"),
        span("stream-auto", 2, 9.5, 12.0, "and a synthetic close"),
        span("stream-manual", 0, 4.0, 9.5, "a different stream"),
    ],
}

PASSAGE = {
    "kind": "media_span",
    "id": "FIXTURE-SPAN",
    "source_id": "FIXTURE",
    "locator": "Speaker, \"Title\" (Channel, 2020-01-01), 00:04–00:09",
    "claim_locator_prefixes": ["Speaker, \"Title\" (Channel, 2020-01-01), 00:04–00:09:"],
    "youtube_id": "abc123XYZ_0",
    "transcript_source": "caption_auto",
    "language": "en",
    "producer": "youtube-corpus",
    "producer_revision": "git:fixture",
    "export_schema": "source_span_interchange@1",
    "source_url": "https://www.youtube.com/watch?v=abc123XYZ_0",
    "license": "synthetic fixture",
    "start_seconds": 4.0,
    "end_seconds": 9.5,
}


def pinned() -> dict:
    passage = dict(PASSAGE)
    segments = se.media_span_segments(EXPORT, passage)[0]
    passage["segment_count"] = len(segments)
    passage["span_sha256"] = se.media_span_hash(segments)
    return passage


class MediaSpanTest(unittest.TestCase):
    def write_export(self, export: dict) -> Path:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "source-span.json"
        path.write_text(json.dumps(export), encoding="utf-8")
        return path

    def test_selects_overlapping_segments_of_pinned_stream(self) -> None:
        segments = se.media_span_segments(EXPORT, PASSAGE)
        self.assertEqual(len(segments), 1)
        self.assertEqual([s["text"] for s in segments[0]], ["the synthetic claim itself"])

    def test_resolves_pinned_span(self) -> None:
        passage = pinned()
        segments, revision = se.resolve_media_span(passage, self.write_export(EXPORT))
        self.assertEqual(revision, "git:fixture")
        self.assertIn("the synthetic claim itself", se.media_span_text(segments))

    def test_hash_ignores_database_ids(self) -> None:
        export = copy.deepcopy(EXPORT)
        for item in export["spans"]:
            item["id"] = "regenerated-" + item["id"]
        passage = pinned()
        se.resolve_media_span(passage, self.write_export(export))

    def test_rejects_changed_transcript(self) -> None:
        export = copy.deepcopy(EXPORT)
        export["spans"][1] = span("stream-auto", 1, 4.0, 9.5, "the synthetic claim, edited")
        with self.assertRaisesRegex(se.SourceEvidenceError, "media span mismatch"):
            se.resolve_media_span(pinned(), self.write_export(export))

    def test_rejects_changed_timing(self) -> None:
        export = copy.deepcopy(EXPORT)
        export["spans"][1]["locator"]["endSeconds"] = 9.4
        with self.assertRaisesRegex(se.SourceEvidenceError, "media span mismatch"):
            se.resolve_media_span(pinned(), self.write_export(export))

    def test_rejects_second_matching_stream(self) -> None:
        export = copy.deepcopy(EXPORT)
        export["sources"].append(
            {
                "id": "stream-auto-reingest",
                "kind": "youtube_transcript",
                "language": "en",
                "metadata": {"youtubeId": "abc123XYZ_0", "transcriptSource": "caption_auto"},
            }
        )
        export["spans"].append(span("stream-auto-reingest", 1, 4.0, 9.5, "a changed re-ingest"))
        with self.assertRaisesRegex(se.SourceEvidenceError, "exactly one"):
            se.resolve_media_span(pinned(), self.write_export(export))

    def test_rejects_inconsistent_content_hash(self) -> None:
        export = copy.deepcopy(EXPORT)
        export["spans"][1]["text"] = "tampered"
        with self.assertRaisesRegex(se.SourceEvidenceError, "contentHash"):
            se.resolve_media_span(pinned(), self.write_export(export))

    def test_rejects_wrong_schema(self) -> None:
        export = dict(EXPORT, schemaVersion=2)
        with self.assertRaisesRegex(se.SourceEvidenceError, "source_span_interchange@1"):
            se.resolve_media_span(pinned(), self.write_export(export))

    def test_manifest_rejects_committed_text(self) -> None:
        passage = dict(pinned(), text="transcript text")
        with self.assertRaisesRegex(se.SourceEvidenceError, "must not commit transcript text"):
            se.validate_media_span_manifest(se.ROOT / "corpus" / "passages" / "fixture.json", passage)

    def test_manifest_accepts_pinned_span(self) -> None:
        se.validate_media_span_manifest(se.ROOT / "corpus" / "passages" / "fixture.json", pinned())



# ---------------------------------------------------------------------------
# web_snapshot (synthetic HTML fixture, no network)
# ---------------------------------------------------------------------------

HTML = """<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>Fixture &amp; title</title>
<style>p { color: red }</style><script>var hidden = "not text";</script></head>
<body>
<p align="center">CAPUT I</p>
<p>Prima pars&nbsp;textus.</p>
<p align="center">CAPUT II</p>
<p>Secunda <i>pars</i>
textus.</p>
<a name="13" id="13">
<p><b>Chapter 13</b>
<p>[1] The first argument &mdash; from motion.
<p>[2] The second argument.</p>
</a> <a name="14" id="14">
<p><b>Chapter 14</b>
<p>[1] Another chapter.</p></a>
<h2 id="article5">Article 5. Whether the fixture works?</h2>
<p>Objection 1. It would seem not.</p>
<div id="answer"><p>I answer that, <span>it does.</span></p></div>
<h3>Reply to Objection 1.</h3>
<p>Thus the reply.</p>
<h2 id="article6">Article 6. Another article?</h2>
<p>Not selected.</p>
</body></html>
""".encode("utf-8")

LIVE_URL = "https://example.org/fixture.htm"
WAYBACK_URL = "https://web.archive.org/web/20260101000000id_/" + LIVE_URL
ARCHIVED = HTML.replace(b"<body>", b"<body><script>injected()</script>")


def web_passage(selector: dict, **extra) -> dict:
    passage = {
        "kind": "web_snapshot",
        "id": "FIXTURE-WEB",
        "source_id": "FIXTURE",
        "locator": "ch. 13",
        "claim_locator_prefixes": ["ch. 13 "],
        "source_url": LIVE_URL,
        "retrieved_at": "2026-10-24T00:00:00Z",
        "sha256": se.sha256_bytes(HTML),
        "encoding": "utf-8",
        "language": "en",
        "license": "synthetic fixture",
        "html_selector": selector,
    }
    passage["text_sha256"] = se.sha256_text(se.extract_web_text(HTML, passage))
    passage.update(extra)
    return passage


class FakeWeb:
    """Serves fixed bytes per URL and checks hashes like fetch_web_bytes."""

    def __init__(self, pages: dict[str, bytes | Exception]) -> None:
        self.pages = pages
        self.requested: list[str] = []

    def __call__(self, url: str, expected: str, label: str) -> bytes:
        self.requested.append(url)
        page = self.pages.get(url, se.SourceEvidenceError(f"{label}: cannot fetch {url}"))
        if isinstance(page, Exception):
            raise page
        if se.sha256_bytes(page) != expected:
            raise se.SourceEvidenceError(f"{label}: byte drift at {url}")
        return page


class WebSnapshotTest(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        patcher = mock.patch.object(se, "WEB_CACHE", Path(directory.name))
        patcher.start()
        self.addCleanup(patcher.stop)

    def extract(self, selector: dict) -> str:
        return se.extract_web_text(HTML, web_passage(selector))

    def test_anchor_range_stops_before_next_anchor(self) -> None:
        text = self.extract({"from": {"anchor": "13"}, "to": {"anchor": "14"}})
        self.assertEqual(text, "Chapter 13\n[1] The first argument — from motion.\n[2] The second argument.")

    def test_text_marker_range_and_entities(self) -> None:
        text = self.extract({"from": {"text": "CAPUT I"}, "to": {"text": "CAPUT II"}})
        self.assertEqual(text, "CAPUT I\nPrima pars textus.")

    def test_heading_runs_to_next_heading_of_same_level(self) -> None:
        text = self.extract({"heading": "Article 5. Whether the fixture works?"})
        self.assertTrue(text.startswith("Article 5."))
        self.assertIn("Reply to Objection 1.\nThus the reply.", text)
        self.assertNotIn("Article 6", text)

    def test_element_id_and_skipped_script(self) -> None:
        self.assertEqual(self.extract({"element_id": "answer"}), "I answer that, it does.")
        self.assertNotIn("hidden", se.render_html_text(se.html_tokens(HTML.decode("utf-8"))))

    def test_element_id_closes_implied_end_tags(self) -> None:
        def select(page: str, element_id: str) -> str:
            passage = {"id": "X", "encoding": "utf-8", "html_selector": {"element_id": element_id}}
            return se.extract_web_text(page.encode("utf-8"), passage)

        cases = [
            ("<div><p id=x>First <b>bold</b><br/>line<p>Second</div><p>Third", "First bold\nline"),
            ("<p id=x>Para<div>Block</div>", "Para"),
            ("<ul><li id=x>One<ul><li>Inner</ul><li>Two</ul>After", "One\nInner"),
            ("<ul><li>Zero<li id=x>One</ul><p>After", "One"),
            ("<ul><li id=x>One</p>more<li>Two</ul>", "One\nmore"),
            ("<dl><dt id=x>Term<dd>Def</dl>", "Term"),
            ("<table><tr><td id=x>A<td>B</table>", "A"),
            ("<div id=x><p>A<p>B<div>C</div></div><p>After", "A\nB\nC"),
        ]
        for page, expected in cases:
            with self.subTest(page=page):
                self.assertEqual(select(page, "x"), expected)

    def test_selector_must_match_exactly_once(self) -> None:
        passage = {"id": "X", "encoding": "utf-8", "html_selector": {"heading": "Missing"}}
        with self.assertRaisesRegex(se.SourceEvidenceError, "matched 0"):
            se.extract_web_text(HTML, passage)

    def test_materializes_pinned_live_page(self) -> None:
        passage = web_passage({"from": {"anchor": "13"}, "to": {"anchor": "14"}})
        text = se.materialize_web_snapshot(passage, use_cache=False, fetch=FakeWeb({LIVE_URL: HTML}))
        self.assertTrue(text.startswith("Chapter 13"))

    def test_rejects_byte_drift_without_fallback(self) -> None:
        passage = web_passage({"from": {"anchor": "13"}})
        drifted = HTML.replace(b"second", b"edited")
        with self.assertRaisesRegex(se.SourceEvidenceError, "byte drift"):
            se.materialize_web_snapshot(passage, use_cache=False, fetch=FakeWeb({LIVE_URL: drifted}))

    def test_falls_back_to_pinned_wayback_capture(self) -> None:
        passage = web_passage(
            {"from": {"anchor": "13"}, "to": {"anchor": "14"}},
            wayback_url=WAYBACK_URL,
            wayback_sha256=se.sha256_bytes(ARCHIVED),
        )
        web = FakeWeb({LIVE_URL: HTML.replace(b"2026", b"2027") + b"<!-- footer 2027 -->", WAYBACK_URL: ARCHIVED})
        with contextlib.redirect_stderr(io.StringIO()) as stderr:
            text = se.materialize_web_snapshot(passage, use_cache=False, fetch=web)
        self.assertEqual(web.requested, [LIVE_URL, WAYBACK_URL])
        self.assertIn("Wayback", stderr.getvalue())
        self.assertTrue(text.startswith("Chapter 13"))

    def test_rejects_drifted_wayback_capture(self) -> None:
        passage = web_passage(
            {"from": {"anchor": "13"}},
            wayback_url=WAYBACK_URL,
            wayback_sha256=se.sha256_bytes(ARCHIVED),
        )
        web = FakeWeb({WAYBACK_URL: ARCHIVED + b" "})
        with self.assertRaisesRegex(se.SourceEvidenceError, "Wayback fallback failed"):
            se.materialize_web_snapshot(passage, use_cache=False, fetch=web)

    def test_rejects_extracted_text_mismatch(self) -> None:
        passage = web_passage({"from": {"anchor": "13"}, "to": {"anchor": "14"}})
        passage["html_selector"] = {"from": {"anchor": "13"}}
        with self.assertRaisesRegex(se.SourceEvidenceError, "extracted text mismatch"):
            se.materialize_web_snapshot(passage, use_cache=False, fetch=FakeWeb({LIVE_URL: HTML}))

    def test_cache_is_used_only_when_hash_matches(self) -> None:
        passage = web_passage({"from": {"anchor": "13"}, "to": {"anchor": "14"}})
        se.materialize_web_snapshot(passage, fetch=FakeWeb({LIVE_URL: HTML}))
        offline = FakeWeb({})
        se.materialize_web_snapshot(passage, fetch=offline)
        self.assertEqual(offline.requested, [])
        se.web_cache_path(passage["sha256"]).write_bytes(b"tampered")
        with self.assertRaisesRegex(se.SourceEvidenceError, "cannot fetch"):
            se.materialize_web_snapshot(passage, fetch=offline)

    def manifest(self, passage: dict) -> None:
        se.validate_web_snapshot_manifest(se.ROOT / "corpus" / "passages" / "fixture.json", passage)

    def test_manifest_accepts_translation_snapshot(self) -> None:
        self.manifest(
            web_passage(
                {"heading": "Article 5. Whether the fixture works?"},
                translation={"translator": "A. Translator", "year": 1920, "edition": "2nd ed."},
                wayback_url=WAYBACK_URL,
                wayback_sha256=se.sha256_bytes(ARCHIVED),
                incipit="Article 5.",
            )
        )

    def test_manifest_rejects_text_and_bad_fields(self) -> None:
        selector = {"from": {"anchor": "13"}}
        bad = [
            ({"text": "page text"}, "must not commit page text"),
            ({"incipit": "x" * 81}, "incipit"),
            ({"translation": {"translator": "A"}}, "translation needs year, edition"),
            ({"wayback_url": "https://web.archive.org/web/2026/" + LIVE_URL, "wayback_sha256": se.sha256_bytes(ARCHIVED)}, "wayback_url"),
            ({"wayback_url": WAYBACK_URL}, "wayback_sha256"),
            ({"retrieved_at": "2026-10-24"}, "retrieved_at"),
            ({"encoding": "no-such-codec"}, "unknown encoding"),
            ({"html_selector": {"heading": "A", "element_id": "b"}}, "html_selector"),
        ]
        for extra, message in bad:
            with self.subTest(message=message), self.assertRaisesRegex(se.SourceEvidenceError, message):
                self.manifest(dict(web_passage(selector), **extra))


class TranslationBasisTest(unittest.TestCase):
    PATH = se.ROOT / "corpus" / "claims" / "fixture.json"
    LATIN = {"id": "LATIN", "kind": None, "source_id": "S", "claim_locator_prefixes": ["q.1 "]}
    ENGLISH = {
        "id": "ENGLISH",
        "kind": "web_snapshot",
        "source_id": "S",
        "claim_locator_prefixes": ["q.2 "],
        "translation": {"translator": "T", "year": 1920, "edition": "E"},
    }

    def check(self, claims: list[dict], bound: dict[str, dict]) -> None:
        se.validate_claim_basis([(self.PATH, claim) for claim in claims], bound)

    def test_translation_claim_needs_basis(self) -> None:
        self.check([{"id": "C", "basis": "translation"}], {"C": self.ENGLISH})
        with self.assertRaisesRegex(se.SourceEvidenceError, "needs basis"):
            self.check([{"id": "C"}], {"C": self.ENGLISH})

    def test_basis_only_on_translations(self) -> None:
        with self.assertRaisesRegex(se.SourceEvidenceError, "only for claims on a translated"):
            self.check([{"id": "C", "basis": "translation"}], {"C": self.LATIN})

    def test_translation_reading_cannot_rival_latin_reading(self) -> None:
        claims = [{"id": "L"}, {"id": "E", "basis": "translation", "interpretation_of": "L"}]
        with self.assertRaisesRegex(se.SourceEvidenceError, "cannot be an alternative"):
            self.check(claims, {"L": self.LATIN, "E": self.ENGLISH})

    def test_web_snapshot_may_not_overlap_pinned_witness(self) -> None:
        path = se.ROOT / "corpus" / "passages" / "fixture.json"
        overlapping = dict(self.ENGLISH, claim_locator_prefixes=["q.1 a.2 "])
        passages = {"LATIN": (path, self.LATIN), "ENGLISH": (path, overlapping)}
        with self.assertRaisesRegex(se.SourceEvidenceError, "overlaps pinned witness LATIN"):
            se.validate_web_snapshot_ranges(passages)
        se.validate_web_snapshot_ranges({"LATIN": (path, self.LATIN), "ENGLISH": (path, self.ENGLISH)})


if __name__ == "__main__":
    unittest.main()
