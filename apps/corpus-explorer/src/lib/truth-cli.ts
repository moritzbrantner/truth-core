import { execFileSync } from "node:child_process";
import path from "node:path";

/** The repository root: Next and `bun test` run in apps/corpus-explorer (bundled code has no stable import.meta.url). */
export const repositoryRoot = path.resolve(process.cwd(), "../..");

let binary: string | undefined;

/**
 * The repository's Rust `truth` CLI (truth/README.md). `TRUTH_CLI` names a
 * prebuilt binary; otherwise the release binary is built once per process,
 * which is an incremental no-op when it is current, so a stale binary never
 * produces the explorer's statuses.
 */
function truthBinary(): string {
  if (!binary) {
    binary = process.env.TRUTH_CLI;
    if (!binary) {
      execFileSync("cargo", ["build", "--locked", "--release", "--quiet", "-p", "truth"], {
        cwd: repositoryRoot,
        stdio: ["ignore", "ignore", "inherit"],
      });
      binary = path.join(repositoryRoot, "target", "release", "truth");
    }
  }
  return binary;
}

/**
 * Run `truth <args>` on the repository and parse its JSON stdout. Closure,
 * statuses and dossiers stay owned by the CLI (#507); the explorer only reads
 * them. Version 1 JSON adds `input_identity`, which the explorer ignores.
 */
export function truthJson(args: string[]): unknown {
  return JSON.parse(
    execFileSync(truthBinary(), ["--json", ...args], {
      cwd: repositoryRoot,
      encoding: "utf8",
      maxBuffer: 64 * 1024 * 1024,
    }),
  );
}
