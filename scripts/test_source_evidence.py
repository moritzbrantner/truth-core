"""Offline tests for media_span evidence (synthetic export, no network, no YouTube)."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
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


if __name__ == "__main__":
    unittest.main()
