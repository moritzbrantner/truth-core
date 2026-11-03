/**
 * Expanded-branch state of the single assumption tree, persisted as repeated `open`
 * query entries. A path is `root` followed by `/<ARGUMENT-ID>:<premise index>` segments.
 */

/** Upper bound on the encoded `open=` entries, well below common static-host URL limits. */
export const MAX_OPEN_QUERY_LENGTH = 4000;

function ancestors(path: string): string[] {
  const segments = path.split("/");
  return segments.slice(1).map((_, index) => segments.slice(0, index + 1).join("/"));
}

function encodedLength(paths: string[]): number {
  return paths.reduce((total, path) => total + "&open=".length + encodeURIComponent(path).length, 0);
}

/**
 * Toggle `path` in the ordered list of open paths. Collapsing a branch also closes its
 * descendants, and entries hidden under a closed ancestor are dropped. When the encoded
 * state still exceeds `maxLength`, the oldest open leaves are closed first, so the branch
 * the user just opened stays visible.
 */
export function toggleOpenPath(current: readonly string[], path: string, maxLength = MAX_OPEN_QUERY_LENGTH): string[] {
  let paths = current.includes(path)
    ? current.filter((entry) => entry !== path && !entry.startsWith(path + "/"))
    : [...current, path];
  const open = new Set(paths);
  paths = paths.filter((entry) => ancestors(entry).every((ancestor) => open.has(ancestor)));
  while (paths.length > 1 && encodedLength(paths) > maxLength) {
    const leaf = paths.find((entry) => !paths.some((other) => other.startsWith(entry + "/")));
    paths = paths.filter((entry) => entry !== leaf);
  }
  return paths;
}
