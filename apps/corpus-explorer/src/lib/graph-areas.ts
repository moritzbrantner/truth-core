/**
 * Areas and lanes of graph statements, for the /graph filters and buckets (#491).
 *
 * The area of a statement is the import area (scripts/root_imports.py,
 * `area_of`) of the module path its Lean namespace names: the longest entry of
 * `AREAS` that prefixes it, otherwise its first directory under `TruthCore/`, or
 * the first two for `TruthCore/Results/<Area>/...`. The build reads `AREAS` from
 * root_imports.py itself, so this module holds no second list of areas.
 */

export const NO_LEAN_AREA = "(no Lean declaration)";

export type Lane = "A" | "B" | "C" | "none";

/**
 * Lane ownership as stated in AGENTS.md ("Lanes and shared files"). Lane B is
 * checked first because its areas sit inside lane A's `Case` and lane C's
 * `Comparison` directories. Everything else under `TruthCore/` is lane C.
 */
const LANE_B_PREFIXES = [
  "History",
  "Greek/NewTestament",
  "Case/Catholicism/StageThree",
  "Results/Case/Catholicism/StageThree",
  "Results/Comparison/Resurrection",
  "Comparison/Resurrection",
];
const LANE_A_PREFIXES = ["Latin", "Case", "Results/Aquinas", "Results/Case"];

export const LANES: ReadonlyArray<{ id: Lane; label: string }> = [
  { id: "A", label: "Lane A · Fourth Way and attributes" },
  { id: "B", label: "Lane B · stage 3" },
  { id: "C", label: "Lane C · everything else" },
  { id: "none", label: "No Lean declaration" },
];

/** Parse the `AREAS` tuple from the text of scripts/root_imports.py. */
export function parseAreas(rootImportsSource: string): string[] {
  const block = /^AREAS\s*=\s*\(([\s\S]*?)^\)/m.exec(rootImportsSource);
  if (!block) {
    throw new Error("scripts/root_imports.py: AREAS tuple not found");
  }
  return [...block[1].matchAll(/^\s*"([^"]+)"/gm)].map((match) => match[1]);
}

function namespaceParts(namespace: string | undefined) {
  if (!namespace) return undefined;
  const parts = namespace.split(".");
  return parts[0] === "TruthCore" && parts.length > 1 ? parts.slice(1) : undefined;
}

const startsWith = (parts: string[], prefix: string) => {
  const head = prefix.split("/");
  return head.length <= parts.length && head.every((part, index) => parts[index] === part);
};

/** Mirrors `area_of` in scripts/root_imports.py, applied to the namespace path. */
export function areaOfNamespace(namespace: string | undefined, areas: readonly string[]): string {
  const parts = namespaceParts(namespace);
  if (!parts) return NO_LEAN_AREA;
  let best = "";
  for (const area of areas) {
    if (startsWith(parts, area) && area.length > best.length) best = area;
  }
  if (best) return best;
  const depth = parts[0] === "Results" && parts.length > 1 ? 2 : 1;
  return parts.slice(0, depth).join("/");
}

export function laneOfNamespace(namespace: string | undefined): Lane {
  const parts = namespaceParts(namespace);
  if (!parts) return "none";
  if (LANE_B_PREFIXES.some((prefix) => startsWith(parts, prefix))) return "B";
  if (LANE_A_PREFIXES.some((prefix) => startsWith(parts, prefix))) return "A";
  return "C";
}
