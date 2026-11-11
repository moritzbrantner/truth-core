//! Port of `source_evidence.validate_manifest`: the per-kind passage manifest
//! schema (text witness, media span, web snapshot, bibliographic span), rule
//! for rule and with Python's messages, so a malformed manifest reports the
//! same first error.

use super::{Obj, Res, get, py_repr, py_str, require, truthy};
use fancy_regex::Regex;
use serde_json::Value;
use std::{collections::BTreeSet, sync::LazyLock};

const MEDIA_EXPORT_SCHEMA: &str = "source_span_interchange@1";
const TRANSCRIPT_SOURCES: &[&str] = &["asr", "caption_auto", "caption_manual"];
const MAX_INCIPIT_CHARS: usize = 80;
const MAX_QUOTATION_CHARS: usize = 300;
const MIN_WHY_BIBLIOGRAPHIC_CHARS: usize = 20;
const MIN_UNAVAILABLE_REASON_CHARS: usize = 20;

fn regex(pattern: &str) -> Regex {
    Regex::new(pattern).expect("manifest pattern")
}

static SHA1_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^[0-9a-f]{40}$"));
static SHA256_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^sha256:[0-9a-f]{64}$"));
static YOUTUBE_ID_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^[A-Za-z0-9_-]{11}$"));
static RETRIEVED_AT_RE: LazyLock<Regex> =
    LazyLock::new(|| regex(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$"));
static WAYBACK_RE: LazyLock<Regex> =
    LazyLock::new(|| regex(r"^https://web\.archive\.org/web/(\d{14})id_/(.+)$"));
static DATE_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^\d{4}-\d{2}-\d{2}$"));
static DOI_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^10\.\d{4,9}/\S+$"));
static HTTP_RE: LazyLock<Regex> = LazyLock::new(|| regex(r"^https?://"));

/// `re.fullmatch` for the anchored patterns above. Python's `$` also matches
/// before one trailing newline, which `fullmatch` then rejects; so does this.
fn full(re: &Regex, value: &str) -> bool {
    !value.ends_with('\n') && re.is_match(value).unwrap_or(false)
}

fn full_str(re: &Regex, value: Option<&Value>) -> bool {
    value.and_then(Value::as_str).is_some_and(|v| full(re, v))
}

/// A Python `int` (JSON integer, not bool).
fn int(value: Option<&Value>) -> Option<i128> {
    match value {
        Some(Value::Number(n)) => n
            .as_i64()
            .map(i128::from)
            .or_else(|| n.as_u64().map(i128::from)),
        _ => None,
    }
}

/// A Python `int` or `float` (not bool).
fn number(value: Option<&Value>) -> Option<f64> {
    match value {
        Some(Value::Number(n)) => n.as_f64(),
        _ => None,
    }
}

fn keys(object: &Obj) -> BTreeSet<&str> {
    object.keys().map(String::as_str).collect()
}

fn set<'a>(items: &[&'a str]) -> BTreeSet<&'a str> {
    items.iter().copied().collect()
}

/// `codecs.lookup` succeeds: Python's name normalization (lowercase, runs of
/// characters other than letters, digits and `.` collapsed to `_`) over the
/// standard codecs and their aliases from `encodings.aliases`. Codecs outside
/// this list (rare Asian or Mac code pages) are reported unknown.
fn known_encoding(name: &str) -> bool {
    let mut normalized = String::new();
    let mut punct = false;
    for c in name.to_lowercase().chars() {
        if c.is_alphanumeric() || c == '.' {
            if punct && !normalized.is_empty() {
                normalized.push('_');
            }
            normalized.push(c);
            punct = false;
        } else {
            punct = true;
        }
    }
    let candidates = [normalized.clone(), normalized.replace('.', "_")];
    candidates.iter().any(|name| {
        CODECS.contains(&name.as_str())
            || ALIASES.contains(&name.as_str())
            || name
                .strip_prefix("iso8859_")
                .or_else(|| name.strip_prefix("iso_8859_"))
                .and_then(|n| n.parse::<u8>().ok())
                .is_some_and(|n| (1..=16).contains(&n) && n != 12)
            || name
                .strip_prefix("windows_")
                .or_else(|| name.strip_prefix("cp"))
                .and_then(|n| n.parse::<u16>().ok())
                .is_some_and(|n| (1250..=1258).contains(&n))
            || name
                .strip_prefix("latin")
                .and_then(|n| n.parse::<u8>().ok())
                .is_some_and(|n| (1..=10).contains(&n))
            || name
                .strip_prefix('l')
                .and_then(|n| n.parse::<u8>().ok())
                .is_some_and(|n| (1..=10).contains(&n))
    })
}

const CODECS: &[&str] = &[
    "ascii",
    "big5",
    "big5hkscs",
    "charmap",
    "cp037",
    "cp1006",
    "cp1026",
    "cp1125",
    "cp1140",
    "cp273",
    "cp424",
    "cp437",
    "cp500",
    "cp720",
    "cp737",
    "cp775",
    "cp850",
    "cp852",
    "cp855",
    "cp856",
    "cp857",
    "cp858",
    "cp860",
    "cp861",
    "cp862",
    "cp863",
    "cp864",
    "cp865",
    "cp866",
    "cp869",
    "cp874",
    "cp875",
    "cp932",
    "cp949",
    "cp950",
    "euc_jis_2004",
    "euc_jisx0213",
    "euc_jp",
    "euc_kr",
    "gb18030",
    "gb2312",
    "gbk",
    "hz",
    "idna",
    "iso2022_jp",
    "iso2022_kr",
    "koi8_r",
    "koi8_t",
    "koi8_u",
    "kz1048",
    "latin_1",
    "mac_cyrillic",
    "mac_greek",
    "mac_iceland",
    "mac_latin2",
    "mac_roman",
    "mac_turkish",
    "mbcs",
    "palmos",
    "ptcp154",
    "punycode",
    "raw_unicode_escape",
    "shift_jis",
    "shift_jis_2004",
    "shift_jisx0213",
    "tis_620",
    "unicode_escape",
    "utf_16",
    "utf_16_be",
    "utf_16_le",
    "utf_32",
    "utf_32_be",
    "utf_32_le",
    "utf_7",
    "utf_8",
    "utf_8_sig",
];

const ALIASES: &[&str] = &[
    "646",
    "8859",
    "ansi_x3.4_1968",
    "ansi_x3_4_1968",
    "ansi_x3.4_1986",
    "cp367",
    "cp65001",
    "cp819",
    "csascii",
    "ibm367",
    "ibm819",
    "iso646_us",
    "iso_646.irv_1991",
    "iso_ir_6",
    "iso_ir_100",
    "csisolatin1",
    "latin",
    "u16",
    "u32",
    "u7",
    "u8",
    "unicode_1_1_utf_7",
    "unicodebigunmarked",
    "unicodelittleunmarked",
    "us",
    "us_ascii",
    "utf",
    "utf16",
    "utf32",
    "utf7",
    "utf8",
    "utf8_ucs2",
    "utf8_ucs4",
    "utf_16be",
    "utf_16le",
    "utf_32be",
    "utf_32le",
    "utf_8_sig",
    "sjis",
    "shiftjis",
    "s_jis",
    "eucjp",
    "ujis",
    "u_jis",
    "euckr",
    "chinese",
    "csbig5",
    "big5_tw",
    "936",
    "cp936",
    "ms936",
    "gb18030_2000",
    "koi8r",
    "ibm437",
    "437",
    "ibm850",
    "850",
    "ibm866",
    "866",
    "macroman",
    "macintosh",
    "maccyrillic",
    "maclatin2",
    "maccentraleurope",
    "mac_centeuro",
    "iso_8859_1_1987",
    "x_mac_japanese",
];

fn validate_claim_locator_prefixes(path: &str, passage: &Obj) -> Res<()> {
    let ok = passage
        .get("claim_locator_prefixes")
        .and_then(Value::as_array)
        .is_some_and(|prefixes| {
            !prefixes.is_empty()
                && prefixes
                    .iter()
                    .all(|p| p.as_str().is_some_and(|p| !p.is_empty()))
        });
    if ok {
        Ok(())
    } else {
        Err(format!(
            "{path}: claim_locator_prefixes must be a non-empty list of strings"
        ))
    }
}

fn validate_media_span(path: &str, passage: &Obj) -> Res<()> {
    require(
        passage,
        &[
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
    )?;
    validate_claim_locator_prefixes(path, passage)?;
    let at = format!("{path}: {}", py_str(passage.get("id")));
    let fail = |message: &str| Err(format!("{at}: {message}"));
    let youtube_id = passage.get("youtube_id").and_then(Value::as_str);
    if !youtube_id.is_some_and(|id| full(&YOUTUBE_ID_RE, id)) {
        return fail("youtube_id must be an 11-character YouTube video id");
    }
    if !passage
        .get("transcript_source")
        .and_then(Value::as_str)
        .is_some_and(|s| TRANSCRIPT_SOURCES.contains(&s))
    {
        return fail(&format!(
            "transcript_source must be one of {}",
            TRANSCRIPT_SOURCES.join(", ")
        ));
    }
    if passage.get("export_schema").and_then(Value::as_str) != Some(MEDIA_EXPORT_SCHEMA) {
        return fail(&format!("export_schema must be {MEDIA_EXPORT_SCHEMA}"));
    }
    if passage.get("producer").and_then(Value::as_str) != Some("youtube-corpus") {
        return fail("producer must be youtube-corpus");
    }
    if !passage
        .get("producer_revision")
        .and_then(Value::as_str)
        .is_some_and(|r| r.starts_with("git:"))
    {
        return fail("producer_revision must be a git:<sha> revision");
    }
    if !py_str(passage.get("source_url")).contains(youtube_id.unwrap_or_default()) {
        return fail("source_url must name the pinned youtube_id");
    }
    let (start, end) = (
        number(passage.get("start_seconds")),
        number(passage.get("end_seconds")),
    );
    if !matches!((start, end), (Some(start), Some(end)) if 0.0 <= start && start < end) {
        return fail("need numeric 0 <= start_seconds < end_seconds");
    }
    if !int(passage.get("segment_count")).is_some_and(|count| count >= 1) {
        return fail("segment_count must be a positive integer");
    }
    if !full_str(&SHA256_RE, passage.get("span_sha256")) {
        return fail("span_sha256 must be sha256:<64 hex digits>");
    }
    if passage.contains_key("text") || passage.contains_key("transcript") {
        return fail("media spans must not commit transcript text");
    }
    Ok(())
}

fn validate_html_selector(at: &str, selector: Option<&Value>) -> Res<()> {
    let Some(selector) = selector
        .and_then(Value::as_object)
        .filter(|s| !s.is_empty())
    else {
        return Err(format!("{at}: html_selector must be an object"));
    };
    let present = keys(selector);
    if present == set(&["element_id"]) || present == set(&["heading"]) {
        let value = selector.values().next().and_then(Value::as_str);
        if !value.is_some_and(|v| !v.is_empty()) {
            return Err(format!(
                "{at}: html_selector value must be a non-empty string"
            ));
        }
        return Ok(());
    }
    if present.contains("from") && present.is_subset(&set(&["from", "to"])) {
        for side in &present {
            let ok = selector[*side].as_object().is_some_and(|marker| {
                marker.len() == 1
                    && marker.iter().all(|(key, value)| {
                        (key == "anchor" || key == "text")
                            && value.as_str().is_some_and(|v| !v.is_empty())
                    })
            });
            if !ok {
                return Err(format!(
                    "{at}: html_selector {side} must be {{\"anchor\": ...}} or {{\"text\": ...}}"
                ));
            }
        }
        return Ok(());
    }
    Err(format!(
        "{at}: html_selector must be {{element_id}}, {{heading}}, or {{from, to?}}"
    ))
}

fn validate_pdf_pages(at: &str, pages: Option<&Value>) -> Res<()> {
    let ok = pages.and_then(Value::as_object).is_some_and(|pages| {
        let present = keys(pages);
        (present == set(&["first", "last"])
            || present == set(&["first", "last", "text_normalization"]))
            && (!pages.contains_key("text_normalization")
                || pages["text_normalization"].as_str() == Some("join_soft_hyphens"))
            && matches!(
                (int(pages.get("first")), int(pages.get("last"))),
                (Some(first), Some(last)) if 1 <= first && first <= last
            )
    });
    if ok {
        Ok(())
    } else {
        Err(format!(
            "{at}: pdf_pages requires positive integer first <= last; \
             optional text_normalization must be join_soft_hyphens"
        ))
    }
}

fn validate_translation(at: &str, translation: &Value) -> Res<()> {
    let Some(translation) = translation.as_object() else {
        return Err(format!("{at}: translation must be an object"));
    };
    let missing: Vec<&str> = ["translator", "year", "edition"]
        .into_iter()
        .filter(|field| match translation.get(*field) {
            None | Some(Value::Null) => true,
            Some(Value::String(s)) => s.is_empty(),
            _ => false,
        })
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!("{at}: translation needs {}", missing.join(", ")))
    }
}

fn validate_web_snapshot(path: &str, passage: &Obj) -> Res<()> {
    require(
        passage,
        &[
            "id",
            "source_id",
            "locator",
            "claim_locator_prefixes",
            "source_url",
            "retrieved_at",
            "sha256",
            "encoding",
            "language",
            "license",
            "text_sha256",
        ],
        path,
    )?;
    validate_claim_locator_prefixes(path, passage)?;
    let at = format!("{path}: {}", py_str(passage.get("id")));
    let fail = |message: String| Err(format!("{at}: {message}"));
    let url = passage.get("source_url").and_then(Value::as_str);
    if !url.is_some_and(|url| HTTP_RE.is_match(url).unwrap_or(false)) {
        return fail("source_url must be an http(s) URL".into());
    }
    if !full_str(&RETRIEVED_AT_RE, passage.get("retrieved_at")) {
        return fail("retrieved_at must be a UTC timestamp YYYY-MM-DDTHH:MM:SSZ".into());
    }
    for field in ["sha256", "text_sha256"] {
        if !full_str(&SHA256_RE, passage.get(field)) {
            return fail(format!("{field} must be sha256:<64 hex digits>"));
        }
    }
    let encoding = passage.get("encoding");
    if !encoding.and_then(Value::as_str).is_some_and(known_encoding) {
        return fail(format!("unknown encoding {}", py_repr(encoding)));
    }
    let formats = ["html_selector", "pdf_pages", "raw_text"];
    if formats.iter().filter(|f| passage.contains_key(**f)).count() != 1 {
        return fail("exactly one of html_selector, pdf_pages and raw_text is required".into());
    }
    if passage.contains_key("pdf_pages") {
        validate_pdf_pages(&at, passage.get("pdf_pages"))?;
    } else if passage.contains_key("html_selector") {
        validate_html_selector(&at, passage.get("html_selector"))?;
    } else if passage.get("raw_text") != Some(&Value::Bool(true)) {
        return fail("raw_text must be true".into());
    }
    if let Some(translation) = get(passage, "translation") {
        validate_translation(&at, translation)?;
    }
    if let Some(wayback) = get(passage, "wayback_url") {
        let matched = wayback
            .as_str()
            .filter(|w| !w.ends_with('\n'))
            .and_then(|w| {
                WAYBACK_RE
                    .captures(w)
                    .ok()
                    .flatten()
                    .and_then(|c| c.get(2).map(|m| m.as_str().to_owned()))
            });
        if matched.as_deref() != url {
            return fail(
                "wayback_url must be https://web.archive.org/web/<14-digit timestamp>id_/<source_url>"
                    .into(),
            );
        }
        if !full_str(&SHA256_RE, passage.get("wayback_sha256")) {
            return fail("wayback_url needs wayback_sha256 of the archived bytes".into());
        }
    } else if passage.contains_key("wayback_sha256") {
        return fail("wayback_sha256 without wayback_url".into());
    }
    if let Some(incipit) = get(passage, "incipit")
        && !incipit
            .as_str()
            .is_some_and(|i| i.chars().count() <= MAX_INCIPIT_CHARS)
    {
        return fail(format!(
            "incipit must be a string of at most {MAX_INCIPIT_CHARS} characters"
        ));
    }
    if passage.contains_key("text") {
        return fail("web snapshots must not commit page text".into());
    }
    if let Some(unavailable) = passage.get("unavailable") {
        let ok = unavailable.as_object().is_some_and(|u| {
            keys(u) == set(&["reason", "since"])
                && full_str(&DATE_RE, u.get("since"))
                && u.get("reason")
                    .and_then(Value::as_str)
                    .is_some_and(|r| r.trim().chars().count() >= MIN_UNAVAILABLE_REASON_CHARS)
        });
        if !ok {
            return fail(format!(
                "unavailable must be {{since: YYYY-MM-DD, reason: why every pinned URL is gone \
                 (at least {MIN_UNAVAILABLE_REASON_CHARS} characters)}}"
            ));
        }
    }
    Ok(())
}

/// Python `valid_isbn`.
fn valid_isbn(value: &str) -> bool {
    let digits: Vec<char> = value
        .chars()
        .filter(|c| *c != '-' && *c != ' ')
        .flat_map(char::to_uppercase)
        .collect();
    let digit = |c: &char| c.to_digit(10);
    if digits.len() == 10
        && digits[..9].iter().all(|c| c.is_ascii_digit())
        && (digits[9].is_ascii_digit() || digits[9] == 'X')
    {
        let total: u32 = digits
            .iter()
            .enumerate()
            .map(|(i, c)| (10 - i as u32) * if *c == 'X' { 10 } else { digit(c).unwrap() })
            .sum();
        return total.is_multiple_of(11);
    }
    if digits.len() == 13 && digits.iter().all(|c| c.is_ascii_digit()) {
        let total: u32 = digits
            .iter()
            .enumerate()
            .map(|(i, c)| if i % 2 == 0 { 1 } else { 3 } * digit(c).unwrap())
            .sum();
        return total.is_multiple_of(10);
    }
    false
}

fn validate_bibliographic(path: &str, passage: &Obj) -> Res<()> {
    require(
        passage,
        &[
            "id",
            "source_id",
            "locator",
            "claim_locator_prefixes",
            "author",
            "title",
            "year",
            "language",
            "why_bibliographic",
        ],
        path,
    )?;
    validate_claim_locator_prefixes(path, passage)?;
    let at = format!("{path}: {}", py_str(passage.get("id")));
    let fail = |message: String| Err(format!("{at}: {message}"));
    for field in ["author", "title", "language"] {
        if !passage.get(field).is_some_and(Value::is_string) {
            return fail(format!("{field} must be a string"));
        }
    }
    if !int(passage.get("year")).is_some_and(|year| (1000..=2100).contains(&year)) {
        return fail("year must be the four-digit publication year of the cited edition".into());
    }
    let nonempty_string = |field: &str| {
        passage
            .get(field)
            .and_then(Value::as_str)
            .is_some_and(|s| !s.is_empty())
    };
    if !nonempty_string("publisher") && !nonempty_string("journal") {
        return fail("a bibliographic span needs a publisher (book) or a journal (article)".into());
    }
    if !truthy(passage.get("isbn")) && !truthy(passage.get("doi")) {
        return fail("a bibliographic span needs an isbn or a doi".into());
    }
    if passage.contains_key("isbn")
        && !passage
            .get("isbn")
            .and_then(Value::as_str)
            .is_some_and(valid_isbn)
    {
        return fail("isbn must be a valid ISBN-10 or ISBN-13".into());
    }
    if passage.contains_key("doi") && !full_str(&DOI_RE, passage.get("doi")) {
        return fail("doi must have the form 10.<registrant>/<suffix>".into());
    }
    if !nonempty_string("pages") && !nonempty_string("section") {
        return fail("a bibliographic span needs an exact pages or section locator".into());
    }
    if !passage
        .get("why_bibliographic")
        .and_then(Value::as_str)
        .is_some_and(|why| why.trim().chars().count() >= MIN_WHY_BIBLIOGRAPHIC_CHARS)
    {
        return fail(
            "why_bibliographic must say why no pinnable witness (public-domain edition, \
             web_snapshot of a legitimately hosted copy) exists"
                .into(),
        );
    }
    if let Some(quotation) = get(passage, "quotation")
        && !quotation
            .as_str()
            .is_some_and(|q| !q.is_empty() && q.chars().count() <= MAX_QUOTATION_CHARS)
    {
        return fail(format!(
            "quotation must be a short quotation of at most {MAX_QUOTATION_CHARS} characters; \
             paraphrase otherwise"
        ));
    }
    if let Some(translation) = get(passage, "translation") {
        validate_translation(&at, translation)?;
    }
    for field in [
        "text",
        "transcript",
        "sha256",
        "text_sha256",
        "git_blob_sha",
        "span_sha256",
    ] {
        if passage.contains_key(field) {
            return fail(format!(
                "a bibliographic span commits no text and claims no byte hash ({field}); \
                 upgrade it to a pinned witness instead"
            ));
        }
    }
    Ok(())
}

/// Python `validate_manifest` for one passage merged with its snapshot.
pub(super) fn validate_manifest(path: &str, passage: &Obj) -> Res<()> {
    let kind = get(passage, "kind");
    match kind.and_then(Value::as_str) {
        Some("bibliographic_span") => return validate_bibliographic(path, passage),
        Some("media_span") => return validate_media_span(path, passage),
        Some("web_snapshot") => return validate_web_snapshot(path, passage),
        Some("text_witness") => {}
        _ if kind.is_none() => {}
        _ => return Err(format!("{path}: unknown passage kind {}", py_repr(kind))),
    }
    require(
        passage,
        &[
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
    )?;
    validate_claim_locator_prefixes(path, passage)?;
    if !full_str(&SHA1_RE, passage.get("revision")) {
        return Err(format!("{path}: revision must be a 40-character Git SHA"));
    }
    if !full_str(&SHA1_RE, passage.get("git_blob_sha")) {
        return Err(format!(
            "{path}: git_blob_sha must be a 40-character Git blob SHA"
        ));
    }
    let fragment = format!(
        "/{}/{}/{}",
        py_str(passage.get("repository")),
        py_str(passage.get("revision")),
        py_str(passage.get("path"))
    );
    if !passage
        .get("source_url")
        .and_then(Value::as_str)
        .is_some_and(|url| url.contains(&fragment))
    {
        return Err(format!(
            "{path}: source_url must pin repository, revision, and path"
        ));
    }
    if let Some(xml_id) = get(passage, "tei_xml_id") {
        if !xml_id.as_str().is_some_and(|id| !id.is_empty()) {
            return Err(format!(
                "{path}: tei_xml_id must be a non-empty string when present"
            ));
        }
        if truthy(passage.get("cts_path")) {
            return Err(format!(
                "{path}: use either cts_path or tei_xml_id, not both"
            ));
        }
    }
    let selectors = match passage.get("cts_path") {
        None => &[][..],
        Some(Value::Array(items)) => items.as_slice(),
        Some(_) => return Err(format!("{path}: cts_path must be a list when present")),
    };
    for selector in selectors {
        let Some(selector) = selector.as_object() else {
            return Err(format!("{path}: cts_path selectors must be objects"));
        };
        if !selector.get("subtype").is_some_and(Value::is_string)
            || !selector.get("n").is_some_and(Value::is_string)
        {
            return Err(format!(
                "{path}: cts_path selectors require string subtype and n"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodings() {
        for name in [
            "utf-8",
            "UTF8",
            "iso-8859-1",
            "ISO_8859-15",
            "latin-1",
            "cp1252",
            "windows-1252",
            "ascii",
            "us-ascii",
        ] {
            assert!(known_encoding(name), "{name}");
        }
        for name in ["utf-9", "iso-8859-12", "klingon", ""] {
            assert!(!known_encoding(name), "{name}");
        }
    }

    #[test]
    fn isbns() {
        assert!(valid_isbn("0-306-40615-2"));
        assert!(valid_isbn("978-0-306-40615-7"));
        assert!(!valid_isbn("978-0-306-40615-8"));
        assert!(valid_isbn("0-8044-2957-x"));
    }
}
