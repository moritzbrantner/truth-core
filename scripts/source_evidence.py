#!/usr/bin/env python3
"""Verify and materialize immutable primary-source evidence for truth-core."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus"
PASSAGES = CORPUS / "passages"
CACHE = ROOT / ".cache" / "truth-core" / "sources"
SHA1_RE = re.compile(r"^[0-9a-f]{40}$")


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


def validate_manifest(path: Path, passage: dict[str, Any]) -> None:
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

    prefixes = passage["claim_locator_prefixes"]
    if (
        not isinstance(prefixes, list)
        or not prefixes
        or any(not isinstance(prefix, str) or not prefix for prefix in prefixes)
    ):
        raise SourceEvidenceError(
            f"{path.relative_to(ROOT)}: claim_locator_prefixes must be a non-empty list of strings"
        )

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
        work_urn = source[1].get("work_urn")
        if not isinstance(work_urn, str) or not passage["edition_urn"].startswith(work_urn + "."):
            raise SourceEvidenceError(
                f"{path.relative_to(ROOT)}: edition_urn is not an edition of {work_urn}"
            )
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


def verify_all() -> int:
    passages = passage_index()
    validate_bindings()
    snapshots: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    for _, passage in passages.values():
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
    print(f"source evidence ok: {len(passages)} passages, {len(snapshots)} immutable source snapshots")
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


def extract_plain_text(data: bytes, passage: dict[str, Any]) -> str:
    try:
        root = ET.fromstring(data)
    except ET.ParseError as exc:
        raise SourceEvidenceError(f"{passage['id']}: source XML is invalid: {exc}") from exc

    cts_path = passage.get("cts_path", [])
    target = find_cts_target(root, cts_path, passage["id"]) if cts_path else root
    text = " ".join(" ".join(target.itertext()).split())
    if not text:
        raise SourceEvidenceError(f"{passage['id']}: extracted passage text is empty")
    return text


def materialize(passage_id: str, output: str | None) -> int:
    passages = passage_index()
    validate_bindings()
    indexed = passages.get(passage_id)
    if indexed is None:
        raise SourceEvidenceError(f"unknown passage id {passage_id}")
    _, passage = indexed

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
    sub.add_parser("verify", help="fetch and hash-check all immutable source snapshots")
    materialize_parser = sub.add_parser(
        "materialize", help="verify and extract one source passage to a local UTF-8 text file"
    )
    materialize_parser.add_argument("passage_id")
    materialize_parser.add_argument("--output")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "check":
            return check()
        if args.command == "verify":
            return verify_all()
        if args.command == "materialize":
            return materialize(args.passage_id, args.output)
        raise AssertionError(f"unexpected command {args.command}")
    except SourceEvidenceError as exc:
        print(f"source evidence error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
