import { readdirSync, readFileSync } from "node:fs";
import path from "node:path";

/**
 * Build-time index of Lean declarations by full name, so a statement or result
 * page can show the declaration it binds to and link to its line on GitHub.
 * A textual scan: it tracks `namespace X` / `end X` and reads declaration
 * headers. It only locates source text; Lean and Comparator remain the
 * authority on what the declaration means.
 */

export type LeanLocation = {
  name: string;
  /** Path relative to the repository root. */
  file: string;
  /** 1-based line of the declaration keyword. */
  line: number;
  /** Preceding doc comment (if any) and the declaration block. */
  snippet: string;
};

const DECLARATION =
  /^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|class|opaque|axiom|instance)\s+([^\s(:{[]+)/;

const repositoryRoot = path.resolve(process.cwd(), "../..");

function leanFiles(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true })
    .flatMap((entry) => {
      const full = path.join(directory, entry.name);
      if (entry.isDirectory()) return leanFiles(full);
      return entry.name.endsWith(".lean") ? [full] : [];
    })
    .sort();
}

/** Lines of the declaration starting at `start`, up to the next column-0 line. */
function blockFrom(lines: string[], start: number) {
  let end = start + 1;
  while (end < lines.length && !/^\S/.test(lines[end])) end += 1;
  while (end > start + 1 && !lines[end - 1].trim()) end -= 1;
  return lines.slice(start, end);
}

/** The `/-- … -/` doc comment that ends directly above line `start`, if any. */
function docCommentAbove(lines: string[], start: number) {
  let end = start - 1;
  while (end >= 0 && lines[end].startsWith("@[")) end -= 1;
  if (end < 0 || !lines[end].trimEnd().endsWith("-/")) return [];
  let begin = end;
  while (begin >= 0 && !lines[begin].trimStart().startsWith("/--")) {
    if (begin < end && lines[begin].includes("-/")) return [];
    begin -= 1;
  }
  return begin >= 0 ? lines.slice(begin, end + 1) : [];
}

export function indexLeanSource(relativeFile: string, text: string): LeanLocation[] {
  const lines = text.split("\n");
  const namespaces: string[] = [];
  const found: LeanLocation[] = [];
  let inBlockComment = 0;
  lines.forEach((line, index) => {
    // Skip `/- … -/` comment bodies (nested), which may contain example syntax.
    const opens = (line.match(/\/-/g) ?? []).length;
    const closes = (line.match(/-\//g) ?? []).length;
    const wasInComment = inBlockComment > 0;
    inBlockComment = Math.max(0, inBlockComment + opens - closes);
    if (wasInComment) return;

    const namespace = /^namespace\s+(\S+)/.exec(line);
    if (namespace) {
      namespaces.push(namespace[1]);
      return;
    }
    const end = /^end\s+(\S+)/.exec(line);
    if (end && namespaces.at(-1) === end[1]) {
      namespaces.pop();
      return;
    }
    const declaration = DECLARATION.exec(line);
    if (!declaration) return;
    const local = declaration[1];
    const name = local.startsWith("_root_.")
      ? local.slice("_root_.".length)
      : [...namespaces, local].join(".");
    found.push({
      name,
      file: relativeFile,
      line: index + 1,
      snippet: [...docCommentAbove(lines, index), ...blockFrom(lines, index)].join("\n"),
    });
  });
  return found;
}

let cached: Map<string, LeanLocation> | null = null;

export function leanIndex(root = repositoryRoot): Map<string, LeanLocation> {
  if (cached && root === repositoryRoot) return cached;
  const index = new Map<string, LeanLocation>();
  for (const file of leanFiles(path.join(root, "TruthCore"))) {
    const relative = path.relative(root, file);
    for (const location of indexLeanSource(relative, readFileSync(file, "utf8"))) {
      if (!index.has(location.name)) index.set(location.name, location);
    }
  }
  if (root === repositoryRoot) cached = index;
  return index;
}

/** The theorem `theorem` as stated in a module (e.g. the frozen Challenge). */
export function theoremInModule(module: string, theorem: string, root = repositoryRoot): LeanLocation | undefined {
  const relative = `${module.split(".").join("/")}.lean`;
  let text: string;
  try {
    text = readFileSync(path.join(root, relative), "utf8");
  } catch {
    return undefined;
  }
  const locations = indexLeanSource(relative, text);
  const local = theorem.split(".").at(-1);
  return locations.find((location) => location.name === theorem) ?? locations.find((location) => location.name.split(".").at(-1) === local);
}
