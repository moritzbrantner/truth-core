"""PDF web snapshots use the existing byte/text integrity boundary."""
import subprocess
import tempfile
from pathlib import Path
import unittest
from unittest import mock

import source_evidence as se


def fixture_pdf(second_text: bytes = b'Second synthetic page.') -> bytes:
    """A generated, two-page, public-domain fixture with a real PDF cross-reference."""
    objects = [
        b'<< /Type /Catalog /Pages 2 0 R >>',
        b'<< /Type /Pages /Kids [3 0 R 4 0 R] /Count 2 >>',
        b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Resources << /Font << /F1 5 0 R >> >> /Contents 6 0 R >>',
        b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Resources << /Font << /F1 5 0 R >> >> /Contents 7 0 R >>',
        b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>',
    ]
    for text in (b'First synthetic page.', second_text):
        stream = b'BT /F1 12 Tf 72 720 Td (' + text + b') Tj ET'
        objects.append(b'<< /Length ' + str(len(stream)).encode() + b' >>\nstream\n' + stream + b'\nendstream')
    result = b'%PDF-1.4\n'
    offsets = [0]
    for index, obj in enumerate(objects, 1):
        offsets.append(len(result))
        result += str(index).encode() + b' 0 obj\n' + obj + b'\nendobj\n'
    start = len(result)
    result += b'xref\n0 8\n0000000000 65535 f \n'
    result += b''.join(f'{offset:010} 00000 n \n'.encode() for offset in offsets[1:])
    return result + f'trailer\n<< /Size 8 /Root 1 0 R >>\nstartxref\n{start}\n%%EOF\n'.encode()


def passage() -> dict:
    return {
        'kind': 'web_snapshot', 'id': 'FIXTURE-PDF', 'source_id': 'FIXTURE',
        'locator': 'print p. 1', 'claim_locator_prefixes': ['print p. 1,'],
        'source_url': 'https://example.org/fixture.pdf', 'retrieved_at': '2026-10-25T00:00:00Z',
        'sha256': se.sha256_bytes(fixture_pdf()), 'encoding': 'utf-8', 'language': 'eng',
        'license': 'Synthetic public-domain fixture', 'pdf_pages': {'first': 1, 'last': 1},
        'text_sha256': se.sha256_text('First synthetic page.'),
    }


class IsolatedPdfEvidenceTest(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        for name, child in (("WEB_CACHE", "trusted"), ("SOURCE_DIAGNOSTICS", "diagnostics")):
            patcher = mock.patch.object(se, name, Path(directory.name) / child)
            patcher.start()
            self.addCleanup(patcher.stop)


class PdfSnapshotTest(IsolatedPdfEvidenceTest):
    def test_materialize_selected_page_and_integrity(self):
        item = passage()
        def fetch(url, expected, label):
            self.assertEqual(expected, se.sha256_bytes(fixture_pdf()))
            return fixture_pdf()
        self.assertEqual(se.materialize_web_snapshot(item, use_cache=False, fetch=fetch), 'First synthetic page.')
        item['pdf_pages'] = {'first': 2, 'last': 2}
        with self.assertRaisesRegex(se.SourceEvidenceError, 'extracted text mismatch'):
            se.materialize_web_snapshot(item, use_cache=False, fetch=fetch)
        item['text_sha256'] = se.sha256_text('Second synthetic page.')
        self.assertEqual(se.materialize_web_snapshot(item, use_cache=False, fetch=fetch), 'Second synthetic page.')

    def test_manifest_requires_exactly_one_selector_and_valid_range(self):
        path = se.ROOT / 'corpus/passages/fixture.json'
        se.validate_web_snapshot_manifest(path, passage())
        for pages in ({'first': 0, 'last': 1}, {'first': 2, 'last': 1}, {'first': True, 'last': 2}, {'first': 1}, {'first': 1, 'last': 2, 'other': 3}):
            with self.subTest(pages=pages), self.assertRaises(se.SourceEvidenceError):
                se.validate_web_snapshot_manifest(path, dict(passage(), pdf_pages=pages))
        with self.assertRaisesRegex(se.SourceEvidenceError, 'exactly one'):
            se.validate_web_snapshot_manifest(path, dict(passage(), html_selector={'heading': 'Title'}))

    def test_rejects_non_pdf_and_out_of_range(self):
        with self.assertRaisesRegex(se.SourceEvidenceError, 'PDF'):
            se.extract_web_text(b'<p>HTML disguised as PDF</p>', passage())
        with self.assertRaises(se.SourceEvidenceError):
            se.extract_web_text(fixture_pdf(), dict(passage(), pdf_pages={'first': 9, 'last': 9}))
        with self.assertRaisesRegex(se.SourceEvidenceError, 'exceeds available'):
            se.extract_web_text(fixture_pdf(), dict(passage(), pdf_pages={'first': 1, 'last': 9}))

    def test_extractor_failure_is_explicit(self):
        for error in (FileNotFoundError(), subprocess.TimeoutExpired('pdftotext', 30)):
            with mock.patch.object(se.subprocess, 'run', side_effect=error), self.assertRaises(se.SourceEvidenceError):
                se.extract_web_text(fixture_pdf(), passage())
        with mock.patch.object(se.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, b'', b'')), self.assertRaisesRegex(se.SourceEvidenceError, 'empty'):
            se.extract_web_text(fixture_pdf(), passage())

    def test_rejects_drift_before_invoking_pdf_tool(self):
        with mock.patch.object(se, 'download', return_value=b'%PDF-1.4 altered'), mock.patch.object(se.subprocess, 'run') as run:
            with self.assertRaisesRegex(se.SourceEvidenceError, 'byte drift'):
                se.materialize_web_snapshot(passage(), use_cache=False)
            run.assert_not_called()

    def test_pdf_tool_errors_including_password_fail_loudly(self):
        with mock.patch.object(se.subprocess, 'run', return_value=subprocess.CompletedProcess([], 1, b'', b'Incorrect password')):
            with self.assertRaisesRegex(se.SourceEvidenceError, 'PDF extraction failed: Incorrect password'):
                se.extract_web_text(fixture_pdf(), passage())

    def test_rejects_a_textless_page_inside_a_larger_range(self):
        item = dict(passage(), pdf_pages={'first': 1, 'last': 2})
        with self.assertRaisesRegex(se.SourceEvidenceError, 'textless'):
            se.extract_web_text(fixture_pdf(second_text=b''), item)


class PdfSoftHyphenTest(IsolatedPdfEvidenceTest):
    # Actual Oppy pp.16/18/20 deltas from Poppler 24.02.0 and 26.01.0.
    # Synthetic surrounding text avoids redistributing the copyrighted chapter.
    old = "\u00adreality r\u00ad\neality, \u00adsingularity” real-time non‐natural\f"
    new = "r\u00adeality \u00adreality, s\u00adingularity” real-time non‐natural\f"
    canonical = "reality reality, singularity” real-time non‐natural"

    def extract(self, text, item):
        result = subprocess.CompletedProcess([], 0, text.encode(), b'')
        with mock.patch.object(se.subprocess, 'run', return_value=result):
            return se.extract_pdf_text(fixture_pdf(), item)

    def normalized_item(self):
        item = passage()
        item['pdf_pages']['text_normalization'] = 'join_soft_hyphens'
        item['text_sha256'] = se.sha256_text(self.canonical)
        return item

    def test_actual_version_deltas_converge_only_when_opted_in(self):
        item = self.normalized_item()
        se.validate_web_snapshot_manifest(se.ROOT / 'corpus/passages/fixture.json', item)
        for text in (self.old, self.new):
            with self.subTest(text=text):
                # Existing witnesses retain exactly the previous extraction.
                self.assertEqual(self.extract(text, passage()), ' '.join(text.split()))
                actual = self.extract(text, item)
                self.assertEqual(actual, self.canonical)
                se.check_web_text(actual, item)

    def test_does_not_join_across_page_boundaries(self):
        item = self.normalized_item()
        item['pdf_pages']['last'] = 2
        self.assertEqual(self.extract("edge\u00ad\fcase\f", item), 'edge case')

    def test_semantic_change_and_raw_byte_drift_still_rejected(self):
        item = self.normalized_item()
        changed = self.extract(self.new.replace('real-time', 'imaginary-time'), item)
        with self.assertRaisesRegex(se.SourceEvidenceError, 'extracted text mismatch'):
            se.check_web_text(changed, item)
        with mock.patch.object(se, 'download', return_value=b'%PDF-1.4 altered'), mock.patch.object(se.subprocess, 'run') as run:
            with self.assertRaisesRegex(se.SourceEvidenceError, 'byte drift'):
                se.materialize_web_snapshot(item, use_cache=False)
            run.assert_not_called()

    def test_unknown_normalization_policy_rejected(self):
        item = self.normalized_item()
        for value in (True, None, 'remove-hyphens'):
            with self.subTest(value=value), self.assertRaises(se.SourceEvidenceError):
                se.validate_web_snapshot_manifest(se.ROOT / 'corpus/passages/fixture.json',
                    dict(item, pdf_pages=dict(item['pdf_pages'], text_normalization=value)))
