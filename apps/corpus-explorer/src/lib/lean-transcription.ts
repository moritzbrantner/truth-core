import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

/**
 * Transcription heuristic (AGENTS.md invariant 16, "a transcription is not a proof").
 *
 * A result is flagged when its Solution proof, with comments removed, the leading
 * `by` dropped and leading `intro`/`intros` steps ignored, is a single application
 * of one explicit hypothesis of the theorem: `exact hBridge a b` or the term
 * `hBridge a b`. This mirrors the first textual check of
 * `python3 scripts/corpus.py frontier` (#159). It is a deterministic text check,
 * not a proof: it misses transcriptions hidden behind further definitions, and a
 * flagged one-step argument can still be a faithful map of its source.
 *
 * It reads Lean sources, so it runs only in server components during the static
 * build, never in the browser.
 */

const OPEN_BRACKETS = "([{⟨";
const CLOSE_BRACKETS = ")]}⟩";
const IDENT = /^[A-Za-z_][\w.']*/;

export function stripLeanComments(text: string) {
  return text.replace(/\/-[\s\S]*?-\//g, " ").replace(/--[^\n]*/g, "");
}

/** Text after `start` up to the next line that begins at column 0. */
function declarationBlock(text: string, start: number) {
  const rest = text.slice(start);
  const match = /\n(?=\S)/.exec(rest);
  return match ? rest.slice(0, match.index) : rest;
}

/** Leading binder groups of a declaration header: bracket, names, type. */
function binderGroups(header: string) {
  const groups: Array<{ bracket: string; names: string[] }> = [];
  let rest = header.trim();
  while (rest && "({[".includes(rest[0])) {
    let depth = 0;
    let end = rest.length - 1;
    for (let index = 0; index < rest.length; index += 1) {
      const char = rest[index];
      if (OPEN_BRACKETS.includes(char)) {
        depth += 1;
      } else if (CLOSE_BRACKETS.includes(char)) {
        depth -= 1;
        if (depth === 0) {
          end = index;
          break;
        }
      }
    }
    const inner = rest.slice(1, end);
    const colon = inner.indexOf(":");
    const names = (colon === -1 ? inner : inner.slice(0, colon)).split(/\s+/).filter(Boolean);
    groups.push({ bracket: rest[0], names });
    rest = rest.slice(end + 1).trim();
  }
  return groups;
}

/**
 * The hypothesis name applied by a single-application proof of `theoremName`,
 * or null when the proof does more than that (or the theorem is not found).
 */
export function singleApplicationOf(solutionSource: string, theoremName: string): string | null {
  const text = stripLeanComments(solutionSource);
  const escaped = theoremName.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const match = new RegExp(`^theorem\\s+${escaped}(?![\\w.'])`, "m").exec(text);
  if (!match) {
    return null;
  }
  const block = declarationBlock(text, match.index + match[0].length);
  const separator = block.indexOf(":=");
  if (separator === -1) {
    return null;
  }
  const hypotheses = new Set(
    binderGroups(block.slice(0, separator))
      .filter((group) => group.bracket === "(")
      .flatMap((group) => group.names),
  );

  const proof = block.slice(separator + 2).trim();
  // A term-mode proof is one expression even when its arguments span several lines.
  const steps = (/^by\b/.test(proof) ? proof.split("\n") : [proof.split(/\s+/).join(" ")])
    .map((line) => line.trim())
    .filter((line) => line && line !== "by");
  if (steps.length && steps[0].startsWith("by ")) {
    steps[0] = steps[0].slice(3).trim();
  }
  const applied = steps.filter((step) => !/^intros?\b/.test(step));
  if (applied.length !== 1) {
    return null;
  }
  const step = applied[0].replace(/^exact\s+/, "").trim();
  const head = IDENT.exec(step)?.[0].split(".")[0];
  return head && hypotheses.has(head) ? head : null;
}

export type TranscriptionResult = {
  id: string;
  solution_module: string;
  theorem: string;
};

export type TranscriptionFlag = {
  resultId: string;
  hypothesis: string;
};

const repositoryRoot = path.resolve(process.cwd(), "../..");

/** Flags every result whose Solution is a single hypothesis application. */
export function transcriptionFlags(
  results: TranscriptionResult[],
  root = repositoryRoot,
): TranscriptionFlag[] {
  return results.flatMap((result) => {
    const file = path.join(root, `${result.solution_module.split(".").join("/")}.lean`);
    if (!existsSync(file)) {
      return [];
    }
    const theoremName = result.theorem.split(".").at(-1) ?? result.theorem;
    const hypothesis = singleApplicationOf(readFileSync(file, "utf8"), theoremName);
    return hypothesis ? [{ resultId: result.id, hypothesis }] : [];
  });
}
