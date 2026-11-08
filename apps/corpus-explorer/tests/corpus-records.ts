import { findStatement, getCorpus, idOf, nameOf } from "../src/lib/corpus";
import { legacyUuid, shortId, type CorpusKind } from "../src/lib/corpus-ids";

/** The uuid of the migrated record of `kind` with this legacy id (deterministic uuid5). */
export function uid(kind: CorpusKind, legacyId: string) {
  return legacyUuid(kind, legacyId);
}

/** Display label of the migrated record, as the explorer shows it in place of the id. */
export function label(kind: CorpusKind, legacyId: string) {
  return nameOf(legacyUuid(kind, legacyId));
}

/** Secondary identifier text (legacy alias · short uuid) the explorer shows under a title. */
export function secondaryId(kind: CorpusKind, legacyId: string) {
  return idOf(legacyUuid(kind, legacyId));
}

/** Escape a regular-expression literal (labels may contain punctuation). */
export function literal(text: string) {
  return new RegExp(text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"));
}

/** The short uuid the explorer shows where only an opaque id is available. */
export function short(kind: CorpusKind, legacyId: string) {
  return shortId(legacyUuid(kind, legacyId));
}

/** The paraphrase of a migrated statement. */
export function paraphrase(legacyId: string) {
  const statement = findStatement(identityCorpus(), legacyUuid("statement", legacyId));
  if (!statement) throw new Error(`Unknown statement ${legacyId}`);
  return statement.paraphrase;
}

let corpus: ReturnType<typeof getCorpus> | undefined;
function identityCorpus() {
  corpus ??= getCorpus();
  return corpus;
}
