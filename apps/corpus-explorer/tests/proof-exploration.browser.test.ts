import { afterAll, beforeAll, expect, test } from "bun:test";
import { chromium, type Browser } from "playwright";
import path from "node:path";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  // Serve the real static export on an OS-assigned port; no mocked corpus or APIs.
  server = Bun.serve({
    port: 0,
    async fetch(request) {
      const requested = decodeURIComponent(new URL(request.url).pathname);
      const pathname = basePath && requested.startsWith(`${basePath}/`) ? requested.slice(basePath.length) : requested;
      const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
      const file = path.resolve(root, `.${relative}`);
      if (!file.startsWith(`${root}${path.sep}`)) {
        return new Response("Not found", { status: 404 });
      }
      const artifact = Bun.file(file);
      if (!(await artifact.exists())) {
        return new Response("Not found", { status: 404 });
      }
      return new Response(artifact);
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

const graphUrl = (query: string) => `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}graph/?${query}`;

test("proof exploration retains exact intermediate, overlays and shareable inspection", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const target = "STMT-PILOT-WITNESS-AND-CONSEQUENCE";
  const intermediate = "STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS";
  const seed = "STMT-SOME-LEAN-PROPOSITION-HOLDS";
  await page.goto(graphUrl(`view=focus&node=${target}&target=${target}&explore=1&proofScope=${seed}&proofBudget=1500`));
  const panel = page.getByRole("region", { name: "Proof exploration results" });
  await panel.getByText(/Exploration complete/).waitFor();
  await page.locator(`[data-id="${target}"] [data-proof-target="true"]`).waitFor();
  await page.locator(`[data-id="${intermediate}"] [data-proof-junction="true"]`).waitFor();
  expect(await panel.getByRole("link", { name: "PILOT-COMPOSED-WITNESS", exact: true }).count()).toBeGreaterThan(0);
  await panel.getByRole("button", { name: intermediate, exact: true }).first().click();
  await page.waitForURL((url) => url.searchParams.get("node") === intermediate);
  expect(new URL(page.url()).searchParams.get("explore")).toBe("1");
  expect(new URL(page.url()).searchParams.get("proofScope")).toBe(seed);
  await page.reload();
  await panel.getByText(/Exploration complete/).waitFor();
  expect(new URL(page.url()).searchParams.get("target")).toBe(target);
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await panel.getByRole("link", { name: "PILOT-COMPOSED-WITNESS", exact: true }).first().click();
  await page.waitForURL((url) => url.pathname === `${basePath}/results/PILOT-COMPOSED-WITNESS/`);
  await page.getByRole("heading", { name: "The advertised theorem", exact: true }).waitFor();
  await page.getByText("Formal consequence only.", { exact: true }).waitFor();
  expect(errors).toEqual([]);
  await page.close();
}, 60000);

test("open interpretation obligation remains a non-meeting and an unverified queue candidate", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const target = "STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION";
  const open = "STMT-PILOT-LOGICAL-SENTENCE-STABLE";
  await page.goto(graphUrl(`view=focus&node=${target}&target=${target}&explore=1&proofBudget=1500`));
  const panel = page.getByRole("region", { name: "Proof exploration results" });
  await panel.getByText(/Exploration complete/).waitFor();
  const blocker = page.locator(`[data-id="${open}"] [data-proof-blocker="true"]`);
  await blocker.waitFor();
  expect(await blocker.getAttribute("data-proof-forward")).toBe("false");
  await panel.getByText("Unverified intermediate lemma candidate", { exact: true }).click();
  await panel.getByText(/Formalization: unformalized/).waitFor();
  await page.getByRole("complementary", { name: "Research obligations" }).getByText(`Unverified intermediate lemma for ${target}`, { exact: true }).waitFor();
  await page.getByLabel("Exploration budget (visits)").fill("1");
  await page.getByRole("button", { name: "Explore proof", exact: true }).click();
  await panel.getByText(/Budget exhausted/).waitFor();
  expect(new URL(page.url()).searchParams.get("proofBudget")).toBe("1");
  await page.close();
}, 60000);
