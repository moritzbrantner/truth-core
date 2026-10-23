#!/usr/bin/env python3
"""Verify and materialize immutable primary-source evidence for truth-core."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Iterable, Iterator

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"
PASSAGES = CORPUS / "passages"
CACHE = ROOT / ".cache" / "truth-core" / "sources"
MEDIA_CACHE = ROOT / ".cache" / "truth-core" / "media"
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
YOUTUBE_ID_RE = re.compile(r"^[A-Za-z0-9_-]{11}$")
MEDIA_SPAN = "media_span"
MEDIA_EXPORT_SCHEMA = "source_span_interchange@1"
TRANSCRIPT_SOURCES = {"caption_manual", "caption_auto", "asr"}


class SourceEvidenceError(Exception):
    pass


def load_json_dir(name: str) -> list[tuple[Path, dict[str, Any]]]:
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted((CORPUS / name).glob("*.json")):
        try:
            record = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise SourceEvidenceError(f"{path.relative_to(ROOT)}: cannot read JSON: {exc}") from exc
        if not isinstance(record, dict):
            raise SourceEvidenceError(f"{path.relative_to(ROOT)}: top-level JSON value must be an object")
        records.append((path, record))
    return records


def require(record: dict[str, Any], fields: list[str], path: Path) -> None:
    missing = [field for field in fields if record.get(field) in (None, "", [])]
    if missing:
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: missing required field(s): {', '.join(missing)}"
        )


def is_media_span(passage: dict[str, Any]) -> bool:
    return passage.get("kind") == MEDIA_SPAN


def validate_claim_locator_prefixes(path: Path, passage: dict[str, Any]) -> None:
    prefixes = passage["claim_locator_prefixes"]
    if (
        not isinstance(prefixes, list)
        or not prefixes
        or any(not isinstance(prefix, str) or not prefix for prefix in prefixes)
    ):
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: claim_locator_prefixes must be a non-empty list of strings"
        )


def validate_media_span_manifest(path: Path, passage: dict[str, Any]) -> None:
    """A media span pins timed transcript segments by hash; no transcript text is stored."""
    require(
        passage,
        [
            "id",
            "source_id",
            "locator",
            "claim_locator_prefixes",
            "youtube_id",
            "transcript_source",
            "language",
            "producer",
            "producer_revision",
            "export_schema",
            "source_url",
            "license",
            "start_seconds",
            "end_seconds",
            "segment_count",
            "span_sha256",
        ],
        path,
    )
    validate_claim_locator_prefixes(path, passage)
    where = f"{path.relative_to(ROOT)}: {passage['id']}"
    if not isinstance(passage["youtube_id"], str) or not YOUTUBE_ID_RE.fullmatch(passage["youtube_id"]):
        raise SourceEvidenceError(f"{where}: youtube_id must be an 11-character YouTube video id")
    if passage["transcript_source"] not in TRANSCRIPT_SOURCES:
        raise SourceEvidenceError(
            f"{where}: transcript_source must be one of {', '.join(sorted(TRANSCRIPT_SOURCES))}"
        )
    if passage["export_schema"] != MEDIA_EXPORT_SCHEMA:
        raise SourceEvidenceError(f"{where}: export_schema must be {MEDIA_EXPORT_SCHEMA}")
    if passage["producer"] != "youtube-corpus":
        raise SourceEvidenceError(f"{where}: producer must be youtube-corpus")
    if not isinstance(passage["producer_revision"], str) or not passage["producer_revision"].startswith("git:"):
        raise SourceEvidenceError(f"{where}: producer_revision must be a git:<sha> revision")
    if passage["youtube_id"] not in str(passage["source_url"]):
        raise SourceEvidenceError(f"{where}: source_url must name the pinned youtube_id")
    start, end = passage["start_seconds"], passage["end_seconds"]
    if (
        isinstance(start, bool)
        or isinstance(end, bool)
        or not isinstance(start, (int, float))
        or not isinstance(end, (int, float))
        or not 0 <= start < end
    ):
        raise SourceEvidenceError(f"{where}: need numeric 0 <= start_seconds < end_seconds")
    count = passage["segment_count"]
    if isinstance(count, bool) or not isinstance(count, int) or count < 1:
        raise SourceEvidenceError(f"{where}: segment_count must be a positive integer")
    if not isinstance(passage["span_sha256"], str) or not SHA256_RE.fullmatch(passage["span_sha256"]):
        raise SourceEvidenceError(f"{where}: span_sha256 must be sha256:<64 hex digits>")
    if "text" in passage or "transcript" in passage:
        raise SourceEvidenceError(f"{where}: media spans must not commit transcript text")


def validate_manifest(path: Path, passage: dict[str, Any]) -> None:
    if is_media_span(passage):
        validate_media_span_manifest(path, passage)
        return
    if passage.get("kind") not in (None, "text_witness"):
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: unknown passage kind {passage.get('kind')!r}"
        )
    require(
        passage,
        [
            "id",
            "source_id",
            "locator",
            "claim_locator_prefixes",
            "edition_urn",
            "language",
            "repository",
            "revision",
            "path",
            "git_blob_sha",
            "source_url",
            "license",
        ],
        path,
    )

    validate_claim_locator_prefixes(path, passage)

    revision = passage["revision"]
    blob_sha = passage["git_blob_sha"]
    if not isinstance(revision, str) or not SHA1_RE.fullmatch(revision):
        raise SourceEvidenceError(f"{path.relative_to(ROOT)}: revision must be a 40-character Git SHA")
    if not isinstance(blob_sha, str) or not SHA1_RE.fullmatch(blob_sha):
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: git_blob_sha must be a 40-character Git blob SHA"
        )

    source_url = passage["source_url"]
    expected_fragment = f"/{passage['repository']}/{revision}/{passage['path']}"
    if not isinstance(source_url, str) or expected_fragment not in source_url:
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: source_url must pin repository, revision, and path"
        )

    xml_id = passage.get("tei_xml_id")
    if xml_id is not None:
        if not isinstance(xml_id, str) or not xml_id:
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: tei_xml_id must be a non-empty string when present"
            )
        if passage.get("cts_path"):
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: use either cts_path or tei_xml_id, not both"
            )

    cts_path = passage.get("cts_path", [])
    if not isinstance(cts_path, list):
        raise SourceEvidenceError(f"{path.relative_to(ROOT)}: cts_path must be a list when present")
    for selector in cts_path:
        if not isinstance(selector, dict):
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: cts_path selectors must be objects"
            )
        if not isinstance(selector.get("subtype"), str) or not isinstance(selector.get("n"), str):
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: cts_path selectors require string subtype and n"
            )


def index_records(
    records: list[tuple[Path, dict[str, Any]]], kind: str
) -> dict[str, tuple[Path, dict[str, Any]]]:
    result: dict[str, tuple[Path, dict[str, Any]]] = {}
    for path, record in records:
        require(record, ["id"], path)
        record_id = record["id"]
        if not isinstance(record_id, str):
            raise SourceEvidenceError(f"{path.relative_to(ROOT)}: id must be a string")
        if record_id in result:
            other = result[record_id][0].relative_to(ROOT)
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: duplicate {kind} id {record_id}; first seen in {other}"
            )
        result[record_id] = (path, record)
    return result


def load_passages() -> list[tuple[Path, dict[str, Any]]]:
    records: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted(PASSAGES.glob("*.json")):
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise SourceEvidenceError(f"{path.relative_to(ROOT)}: cannot read JSON: {exc}") from exc
        if not isinstance(manifest, dict):
            raise SourceEvidenceError(f"{path.relative_to(ROOT)}: top-level JSON value must be an object")
        snapshot = manifest.get("snapshot")
        passage_records = manifest.get("passages")
        if not isinstance(snapshot, dict) or not isinstance(passage_records, list) or not passage_records:
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: expected snapshot object and non-empty passages list"
            )
        for passage in passage_records:
            if not isinstance(passage, dict):
                raise SourceEvidenceError(f"{path.relative_to(ROOT)}: passages entries must be objects")
            merged = {**snapshot, **passage}
            records.append((path, merged))
    return records


def passage_index() -> dict[str, tuple[Path, dict[str, Any]]]:
    passages = load_passages()
    for path, passage in passages:
        validate_manifest(path, passage)
    return index_records(passages, "passage")


def validate_media_span_source(
    path: Path, passage: dict[str, Any], source: tuple[Path, dict[str, Any]]
) -> None:
    if source[1].get("kind") != "media_recording":
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: media span {passage['id']} needs a media_recording source"
        )
    if source[1].get("youtube_id") != passage["youtube_id"]:
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: media span {passage['id']} youtube_id disagrees "
            f"with source {passage['source_id']}"
        )


def validate_text_witness_source(
    path: Path, passage: dict[str, Any], source: tuple[Path, dict[str, Any]]
) -> None:
    if source[1].get("kind") == "media_recording":
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: text witness {passage['id']} cannot cite a media_recording source"
        )
    work_urn = source[1].get("work_urn")
    # CTS edition URNs extend the work URN. Works outside CTS (e.g. SCTA)
    # instead list their admitted edition identifiers explicitly.
    listed_editions = source[1].get("edition_urns", [])
    if not isinstance(listed_editions, list):
        raise SourceEvidenceError(
            f"{source[0].relative_to(ROOT)}: edition_urns must be a list when present"
        )
    if not isinstance(work_urn, str) or not (
        passage["edition_urn"].startswith(work_urn + ".")
        or passage["edition_urn"] in listed_editions
    ):
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: edition_urn is not an edition of {work_urn}"
        )


def validate_bindings() -> tuple[int, int]:
    sources = index_records(load_json_dir("sources"), "source")
    passages = passage_index()
    claims = load_json_dir("claims")

    seen_prefixes: dict[tuple[str, str], str] = {}
    for path, passage in passages.values():
        source = sources.get(passage["source_id"])
        if source is None:
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: unknown source_id {passage['source_id']}"
            )
        if is_media_span(passage):
            validate_media_span_source(path, passage, source)
        else:
            validate_text_witness_source(path, passage, source)
        for prefix in passage["claim_locator_prefixes"]:
            key = (passage["source_id"], prefix)
            if key in seen_prefixes:
                raise SourceEvidenceError(
                    f"{path.relative_to(ROOT)}: locator prefix {prefix!r} overlaps "
                    f"with passage {seen_prefixes[key]}"
                )
            seen_prefixes[key] = passage["id"]

    for path, claim in claims:
        require(claim, ["id", "source_id", "locator"], path)
        matches = [
            passage
            for _, passage in passages.values()
            if passage["source_id"] == claim["source_id"]
            and any(claim["locator"].startswith(prefix) for prefix in passage["claim_locator_prefixes"])
        ]
        if len(matches) != 1:
            ids = ", ".join(passage["id"] for passage in matches) or "none"
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: claim must resolve to exactly one source passage; "
                f"matched {len(matches)} ({ids})"
            )

    return len(passages), len(claims)


def git_blob_sha(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def fetch_source(passage: dict[str, Any], *, attempts: int = 3) -> bytes:
    last_error: Exception | None = None
    request = urllib.request.Request(
        passage["source_url"],
        headers={"User-Agent": "truth-core-source-evidence/1"},
    )

    for attempt in range(attempts):
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                data = response.read()
            actual = git_blob_sha(data)
            expected = passage["git_blob_sha"]
            if actual != expected:
                raise SourceEvidenceError(
                    f"{passage['id']}: source blob mismatch: expected {expected}, got {actual}"
                )
            return data
        except (urllib.error.URLError, TimeoutError, SourceEvidenceError) as exc:
            last_error = exc
            if attempt + 1 < attempts:
                time.sleep(1 + attempt)

    raise SourceEvidenceError(f"{passage['id']}: cannot verify source witness: {last_error}")


# ---------------------------------------------------------------------------
# Media spans: timed transcript segments from a youtube-corpus export
# ---------------------------------------------------------------------------


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def media_export_cache_path() -> Path:
    """The cached whole-corpus youtube-corpus source-span export."""
    return MEDIA_CACHE / "source-span.json"


def load_media_export(path: Path) -> dict[str, Any]:
    try:
        export = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceEvidenceError(f"{path}: cannot read source-span export: {exc}") from exc
    schema = f"{export.get('schema')}@{export.get('schemaVersion')}"
    if schema != MEDIA_EXPORT_SCHEMA:
        raise SourceEvidenceError(f"{path}: expected {MEDIA_EXPORT_SCHEMA}, got {schema}")
    if not isinstance(export.get("sources"), list) or not isinstance(export.get("spans"), list):
        raise SourceEvidenceError(f"{path}: source-span export needs sources and spans lists")
    return export


def media_span_segments(export: dict[str, Any], passage: dict[str, Any]) -> list[list[dict[str, Any]]]:
    """Return, per matching transcript stream, the timed segments overlapping the span.

    A stream matches when its youtube id, transcript source and language equal the
    pinned ones. A segment belongs to the span when its interval overlaps
    [start_seconds, end_seconds).
    """
    start, end = passage["start_seconds"], passage["end_seconds"]
    streams = [
        source["id"]
        for source in export["sources"]
        if source.get("kind") == "youtube_transcript"
        and source.get("metadata", {}).get("youtubeId") == passage["youtube_id"]
        and source.get("metadata", {}).get("transcriptSource") == passage["transcript_source"]
        and source.get("language") == passage["language"]
    ]
    result = []
    for stream_id in streams:
        segments = []
        for span in export["spans"]:
            locator = span.get("locator", {})
            if span.get("sourceId") != stream_id or locator.get("kind") != "timed":
                continue
            seg_start, seg_end = locator.get("startSeconds"), locator.get("endSeconds")
            if seg_start is None or seg_end is None or not (seg_start < end and seg_end > start):
                continue
            text = span.get("text")
            if not isinstance(text, str):
                raise SourceEvidenceError(f"{passage['id']}: export span {span.get('id')} has no text")
            if span.get("contentHash") != sha256_text(text):
                raise SourceEvidenceError(
                    f"{passage['id']}: export span {span.get('id')} contentHash does not match its text"
                )
            segments.append(
                {
                    "segmentIndex": locator.get("segmentIndex"),
                    "startSeconds": seg_start,
                    "endSeconds": seg_end,
                    "text": text,
                }
            )
        segments.sort(key=lambda segment: (segment["startSeconds"], segment["segmentIndex"]))
        if segments:
            result.append(segments)
    return result


def media_span_hash(segments: list[dict[str, Any]]) -> str:
    """Hash of the span: canonical JSON over each segment's index, timing and text hash.

    Database ids are excluded because they differ between ingests of the same video.
    """
    material = [
        {
            "endSeconds": segment["endSeconds"],
            "segmentIndex": segment["segmentIndex"],
            "startSeconds": segment["startSeconds"],
            "textHash": sha256_text(segment["text"]),
        }
        for segment in segments
    ]
    canonical = json.dumps(material, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return sha256_text(canonical)


def regenerate_media_export(passage: dict[str, Any]) -> Path | None:
    """Regenerate the export with a local youtube-corpus checkout, if one is configured.

    Needs YOUTUBE_CORPUS_DIR (a checkout with a built release binary) and the
    DATABASE_URL of a corpus into which the video was ingested.
    """
    directory = os.environ.get("YOUTUBE_CORPUS_DIR")
    if not directory:
        return None
    checkout = Path(directory)
    binary = checkout / "target" / "release" / "youtube-corpus"
    if not binary.is_file():
        raise SourceEvidenceError(f"{binary}: build youtube-corpus first (cargo build --release)")
    revision = subprocess.run(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    output = media_export_cache_path()
    output.parent.mkdir(parents=True, exist_ok=True)
    completed = subprocess.run(
        [
            str(binary),
            "export",
            "--format",
            "source-span",
            "--producer-revision",
            f"git:{revision}",
            "--output",
            str(output),
        ],
        cwd=checkout,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise SourceEvidenceError(
            f"{passage['id']}: youtube-corpus export failed: {completed.stderr.strip()}"
        )
    return output


def resolve_media_span(passage: dict[str, Any], export_path: Path | None) -> tuple[list[dict[str, Any]], str]:
    """Find the pinned span in an export and reject any hash mismatch.

    Lookup order: an explicit --export file, the local cache, then a fresh export
    from YOUTUBE_CORPUS_DIR. Returns the segments and the export's producer revision.
    """
    candidates = [export_path] if export_path else []
    cached = media_export_cache_path()
    if not export_path:
        if cached.is_file():
            candidates.append(cached)
        else:
            regenerated = regenerate_media_export(passage)
            if regenerated:
                candidates.append(regenerated)
    if not candidates:
        raise SourceEvidenceError(
            f"{passage['id']}: no source-span export for {passage['youtube_id']}; pass --export, "
            f"place one at {cached.relative_to(ROOT)}, or set YOUTUBE_CORPUS_DIR"
        )
    export = load_media_export(candidates[0])
    streams = media_span_segments(export, passage)
    if not streams:
        raise SourceEvidenceError(
            f"{passage['id']}: export {candidates[0]} has no {passage['transcript_source']} "
            f"{passage['language']} segments of {passage['youtube_id']} in the span"
        )
    hashes = []
    for segments in streams:
        actual = media_span_hash(segments)
        if actual == passage["span_sha256"] and len(segments) == passage["segment_count"]:
            return segments, str(export.get("producer", {}).get("revision", ""))
        hashes.append(f"{actual} ({len(segments)} segments)")
    raise SourceEvidenceError(
        f"{passage['id']}: media span mismatch: expected {passage['span_sha256']} "
        f"({passage['segment_count']} segments), got {', '.join(hashes)}"
    )


def format_timestamp(seconds: float) -> str:
    whole = int(seconds)
    hours, rest = divmod(whole, 3600)
    minutes, secs = divmod(rest, 60)
    fraction = f"{seconds - whole:.2f}"[1:]
    stamp = f"{minutes:02d}:{secs:02d}{fraction}"
    return f"{hours}:{stamp}" if hours else stamp


def media_span_text(segments: list[dict[str, Any]]) -> str:
    return "\n".join(
        f"[{format_timestamp(segment['startSeconds'])}–{format_timestamp(segment['endSeconds'])}] "
        f"{' '.join(segment['text'].split())}"
        for segment in segments
    )


def verify_all(export_path: Path | None = None) -> int:
    passages = passage_index()
    validate_bindings()
    snapshots: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    media_verified = 0
    media_skipped = []
    for _, passage in passages.values():
        if is_media_span(passage):
            cached = media_export_cache_path()
            if export_path is None and not cached.is_file():
                media_skipped.append(passage["id"])
                continue
            resolve_media_span(passage, export_path)
            media_verified += 1
            print(f"verified media span {passage['id']} ({passage['span_sha256'][7:19]})")
            continue
        key = (
            passage["repository"],
            passage["revision"],
            passage["path"],
            passage["git_blob_sha"],
        )
        snapshots.setdefault(key, passage)

    for passage in snapshots.values():
        fetch_source(passage)
        print(
            f"verified {passage['repository']}@{passage['revision'][:12]}:"
            f"{passage['path']} ({passage['git_blob_sha'][:12]})"
        )
    if media_skipped:
        # YouTube is never fetched here: media spans are re-verified only from a
        # local source-span export (see `materialize`).
        print(
            f"media spans not re-verified (no local source-span export): {', '.join(media_skipped)}"
        )
    print(
        f"source evidence ok: {len(passages)} passages, {len(snapshots)} immutable source snapshots, "
        f"{media_verified} media spans verified"
    )
    return 0


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def find_cts_target(root: ET.Element, cts_path: list[dict[str, str]], passage_id: str) -> ET.Element:
    current = root
    for selector in cts_path:
        matches = [
            element
            for element in current.iter()
            if local_name(element.tag) == "div"
            and element.get("subtype") == selector["subtype"]
            and element.get("n") == selector["n"]
        ]
        if len(matches) != 1:
            raise SourceEvidenceError(
                f"{passage_id}: CTS selector {selector!r} matched {len(matches)} elements"
            )
        current = matches[0]
    return current


XML_ID = "{http://www.w3.org/XML/1998/namespace}id"
# Marks a TEI `<lb break="no"/>`: the word continues across the line break.
WORD_JOIN = object()


def find_xml_id_target(root: ET.Element, xml_id: str, passage_id: str) -> ET.Element:
    matches = [element for element in root.iter() if element.get(XML_ID) == xml_id]
    if len(matches) != 1:
        raise SourceEvidenceError(
            f"{passage_id}: tei_xml_id {xml_id!r} matched {len(matches)} elements"
        )
    return matches[0]


def iter_text(element: ET.Element) -> Iterator[str | object]:
    """Like ElementTree.itertext, but yields WORD_JOIN at `<lb break="no"/>`."""
    if element.text:
        yield element.text
    for child in element:
        if local_name(child.tag) == "lb" and child.get("break") == "no":
            yield WORD_JOIN
        else:
            yield from iter_text(child)
        if child.tail:
            yield child.tail


def join_text(pieces: Iterable[str | object]) -> str:
    chunks: list[list[str]] = [[]]
    for piece in pieces:
        if piece is WORD_JOIN:
            chunks.append([])
        else:
            chunks[-1].append(str(piece))
    text = ""
    for index, chunk in enumerate(chunks):
        joined = " ".join(chunk)
        text = joined if index == 0 else text.rstrip() + joined.lstrip()
    return " ".join(text.split())


def extract_plain_text(data: bytes, passage: dict[str, Any]) -> str:
    try:
        root = ET.fromstring(data)
    except ET.ParseError as exc:
        raise SourceEvidenceError(f"{passage['id']}: source XML is invalid: {exc}") from exc

    cts_path = passage.get("cts_path", [])
    xml_id = passage.get("tei_xml_id")
    if xml_id:
        target = find_xml_id_target(root, xml_id, passage["id"])
    elif cts_path:
        target = find_cts_target(root, cts_path, passage["id"])
    else:
        target = root
    text = join_text(iter_text(target))
    if not text:
        raise SourceEvidenceError(f"{passage['id']}: extracted passage text is empty")
    return text


def materialize(passage_id: str, output: str | None, export: str | None = None) -> int:
    passages = passage_index()
    validate_bindings()
    indexed = passages.get(passage_id)
    if indexed is None:
        raise SourceEvidenceError(f"unknown passage id {passage_id}")
    _, passage = indexed

    if is_media_span(passage):
        segments, producer_revision = resolve_media_span(passage, Path(export) if export else None)
        if producer_revision != passage["producer_revision"]:
            print(
                f"note: export producer revision {producer_revision} differs from pinned "
                f"{passage['producer_revision']}; the span hash still matches",
                file=sys.stderr,
            )
        text = media_span_text(segments)
    else:
        if export:
            raise SourceEvidenceError(f"{passage_id}: --export applies only to media spans")
        data = fetch_source(passage)
        text = extract_plain_text(data, passage)

    if output:
        output_path = Path(output)
        if not output_path.is_absolute():
            output_path = ROOT / output_path
    else:
        CACHE.mkdir(parents=True, exist_ok=True)
        output_path = CACHE / f"{passage_id}.txt"

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(text + "\n", encoding="utf-8")
    print(output_path)
    return 0


def check() -> int:
    passage_count, claim_count = validate_bindings()
    print(
        f"source evidence manifests ok: {passage_count} passages; "
        f"{claim_count} formalized claims have unambiguous source evidence"
    )
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Verify and materialize immutable primary-source evidence"
    )
    sub = result.add_subparsers(dest="command", required=True)
    sub.add_parser("check", help="validate passage manifests and claim bindings without network access")
    verify_parser = sub.add_parser(
        "verify",
        help="fetch and hash-check all immutable source snapshots; media spans only from a local export",
    )
    verify_parser.add_argument("--export", help="youtube-corpus source-span export for media spans")
    materialize_parser = sub.add_parser(
        "materialize", help="verify and extract one source passage to a local UTF-8 text file"
    )
    materialize_parser.add_argument("passage_id")
    materialize_parser.add_argument("--output")
    materialize_parser.add_argument(
        "--export", help="youtube-corpus source-span export to read a media span from"
    )
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "check":
            return check()
        if args.command == "verify":
            return verify_all(Path(args.export) if args.export else None)
        if args.command == "materialize":
            return materialize(args.passage_id, args.output, args.export)
        raise AssertionError(f"unexpected command {args.command}")
    except SourceEvidenceError as exc:
        print(f"source evidence error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
