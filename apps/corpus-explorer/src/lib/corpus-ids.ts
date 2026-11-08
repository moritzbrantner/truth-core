/**
 * Opaque corpus identity (owner decision 2026-11-07; `scripts/corpus_ids.py`).
 *
 * Every record is identified by a uuid. A migrated record keeps its readable
 * former id as `legacy_id` and has a display `label`. Its uuid is
 * `uuid5(NAMESPACE, "<kind>:<legacy_id>")`, so code that names a canonical
 * record (a default root, a guide's chain) resolves it with `legacyUuid`
 * without loading the corpus. Never infer a record's kind from its id.
 */
export const CORPUS_ID_NAMESPACE = "d140b0b2-f5a2-4598-9bf7-f3380fb20491";

export type CorpusKind =
  | "source"
  | "statement"
  | "claim"
  | "inference"
  | "argument"
  | "relation"
  | "candidate"
  | "result"
  | "definition"
  | "disambiguation"
  | "attempt"
  | "model"
  | "configuration"
  | "passage";

export const UUID_PATTERN = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/;

export function isUuid(value: unknown): value is string {
  return typeof value === "string" && UUID_PATTERN.test(value);
}

/** SHA-1 in plain JS so the helper also runs in client bundles (no node:crypto). */
function sha1(bytes: Uint8Array) {
  const length = bytes.length;
  const padded = new Uint8Array(((length + 9 + 63) >> 6) << 6);
  padded.set(bytes);
  padded[length] = 0x80;
  const view = new DataView(padded.buffer);
  view.setUint32(padded.length - 4, length * 8);
  view.setUint32(padded.length - 8, Math.floor((length * 8) / 2 ** 32));
  const h = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
  const w = new Uint32Array(80);
  const rotl = (x: number, n: number) => (x << n) | (x >>> (32 - n));
  for (let offset = 0; offset < padded.length; offset += 64) {
    for (let i = 0; i < 16; i++) w[i] = view.getUint32(offset + i * 4);
    for (let i = 16; i < 80; i++) w[i] = rotl(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1);
    let [a, b, c, d, e] = h;
    for (let i = 0; i < 80; i++) {
      const [f, k] =
        i < 20 ? [(b & c) | (~b & d), 0x5a827999]
        : i < 40 ? [b ^ c ^ d, 0x6ed9eba1]
        : i < 60 ? [(b & c) | (b & d) | (c & d), 0x8f1bbcdc]
        : [b ^ c ^ d, 0xca62c1d6];
      const temp = (rotl(a, 5) + f + e + k + w[i]) >>> 0;
      e = d;
      d = c;
      c = rotl(b, 30) >>> 0;
      b = a;
      a = temp;
    }
    h[0] = (h[0] + a) >>> 0;
    h[1] = (h[1] + b) >>> 0;
    h[2] = (h[2] + c) >>> 0;
    h[3] = (h[3] + d) >>> 0;
    h[4] = (h[4] + e) >>> 0;
  }
  const out = new Uint8Array(20);
  const outView = new DataView(out.buffer);
  h.forEach((value, index) => outView.setUint32(index * 4, value));
  return out;
}

const uuidCache = new Map<string, string>();

function uuid5(namespace: string, name: string) {
  const key = `${namespace}|${name}`;
  const cached = uuidCache.get(key);
  if (cached) return cached;
  const namespaceHex = namespace.replaceAll("-", "");
  const nameBytes = new TextEncoder().encode(name);
  const input = new Uint8Array(16 + nameBytes.length);
  for (let i = 0; i < 16; i++) input[i] = parseInt(namespaceHex.slice(i * 2, i * 2 + 2), 16);
  input.set(nameBytes, 16);
  const hash = sha1(input);
  hash[6] = (hash[6] & 0x0f) | 0x50;
  hash[8] = (hash[8] & 0x3f) | 0x80;
  const hex = Array.from(hash.subarray(0, 16), (byte) => byte.toString(16).padStart(2, "0")).join("");
  const id = `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
  uuidCache.set(key, id);
  return id;
}

/** The deterministic uuid of the migrated record of `kind` whose legacy id is `legacyId`. */
export function legacyUuid(kind: CorpusKind, legacyId: string) {
  return uuid5(CORPUS_ID_NAMESPACE, `${kind}:${legacyId}`);
}

/** The first eight hex digits of a uuid; any other id unchanged. */
export function shortId(id: string) {
  return isUuid(id) ? id.slice(0, 8) : id;
}

/** Identity fields every migrated record carries. */
export type RecordIdentity = { id: string; label?: string; legacy_id?: string };

/** Display name of a record: its label, else its id. */
export function recordLabel(record: RecordIdentity | undefined, fallbackId = "") {
  return record?.label ?? record?.id ?? fallbackId;
}

/** Secondary identifier text: the legacy id when there is one, else the short uuid. */
export function recordSecondaryId(record: RecordIdentity) {
  return record.legacy_id ?? shortId(record.id);
}

/**
 * Record ids cited in prose: bare uuids, and legacy aliases with a readable
 * prefix (`STMT-…`, `DEF-…`, `DISAMB-…`). The prefixes only find candidate
 * tokens in text; each token resolves through `legacy_id` lookup, never by
 * assuming a kind from its spelling.
 */
const CITED_TOKEN = /\b(?:[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|(?:STMT|DEF|DISAMB)-[A-Z0-9]+(?:-[A-Z0-9]+)*)\b/g;

export function citedTokens(text: string): string[] {
  return text.match(CITED_TOKEN) ?? [];
}

/** Map from each record's id and legacy alias to its id, for resolving cited tokens. */
export function aliasMap(records: Iterable<RecordIdentity>) {
  const aliases = new Map<string, string>();
  for (const record of records) {
    aliases.set(record.id, record.id);
    if (record.legacy_id && !aliases.has(record.legacy_id)) aliases.set(record.legacy_id, record.id);
  }
  return aliases;
}

/** The ids of `records` that `text` cites, by uuid or legacy alias, in order of first citation. */
export function citedRecordIds(text: string, aliases: Map<string, string>) {
  return [...new Set(citedTokens(text).flatMap((token) => aliases.get(token) ?? []))];
}

/** Split prose into text and cited-record segments, for linkification. */
export function splitCitations(text: string, aliases: Map<string, string>) {
  const segments: Array<{ text: string; id?: string }> = [];
  let last = 0;
  for (const match of text.matchAll(CITED_TOKEN)) {
    const id = aliases.get(match[0]);
    if (!id || match.index === undefined) continue;
    if (match.index > last) segments.push({ text: text.slice(last, match.index) });
    segments.push({ text: match[0], id });
    last = match.index + match[0].length;
  }
  if (last < text.length) segments.push({ text: text.slice(last) });
  return segments;
}
