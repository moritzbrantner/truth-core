import { expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../../../../", import.meta.url));

function buildTask(pages: string) {
  const report = JSON.parse(execFileSync("bun", ["run", "build", "--dry=json"], {
    cwd: root,
    env: { ...process.env, GITHUB_PAGES: pages },
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  }));
  return report.tasks.find((task: { taskId: string }) => task.taskId === "@truth-core/corpus-explorer#build");
}

test("the real root build passes the Pages flag and separates deployment-mode cache keys", () => {
  const normal = buildTask("false");
  const pages = buildTask("true");
  expect(pages.environmentVariables.specified.env).toContain("GITHUB_PAGES");
  expect(normal.hash).not.toBe(pages.hash);
});
