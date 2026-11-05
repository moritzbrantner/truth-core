import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser, type Page } from "playwright";
import { forestPaths, type ForestEvent, type ForestState } from "./forest-story-model";

// A bounded, opt-in story suite against the same static export as the existing
// forest browser tests. Only the expected transitions live in the XState model.
let browser: Browser;
let server: ReturnType<typeof Bun.serve> | undefined;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const testOrigin = process.env.FOREST_TARGET_ORIGIN;

beforeAll(async () => {
  if (!testOrigin) {
    server = Bun.serve({ port: 0, async fetch(request) {
      let pathname = decodeURIComponent(new URL(request.url).pathname);
      if (basePath && pathname.startsWith(`${basePath}/`)) { pathname = pathname.slice(basePath.length); }
      const file = path.resolve(root, `.${pathname.endsWith("/") ? `${pathname}index.html` : pathname}`);
      if (!file.startsWith(`${root}${path.sep}`) || !(await Bun.file(file).exists())) {
        return new Response("Not found", { status: 404 });
      }
      return new Response(Bun.file(file));
    } });
  }
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

async function assertState(page: Page, state: ForestState) {
  await page.getByRole("heading", { name: "Argument forest", exact: true }).waitFor();
  await page.getByRole("region", { name: "Primary conclusion" }).waitFor();
  const params = new URL(page.url()).searchParams;
  if (state === "overview") {
    expect(params.has("sel")).toBe(false);
    expect(params.has("flip")).toBe(false);
    await page.getByRole("region", { name: "Compared conclusion" }).waitFor();
  } else if (state === "selected") {
    expect(params.has("sel")).toBe(true);
    expect(params.has("flip")).toBe(false);
    await page.getByRole("region", { name: "Compared conclusion" }).waitFor();
  } else {
    expect(params.has("sel")).toBe(true);
    expect(params.get("flip")).toBe("1");
    await page.getByRole("region", { name: "Hypothetical negation" }).waitFor();
  }
}

async function perform(page: Page, event: ForestEvent) {
  switch (event) {
    case "SELECT":
      await page.getByRole("region", { name: "Primary conclusion" })
        .getByRole("button", { name: /^Select proposition:/ }).last().click();
      await page.waitForURL((url) => url.searchParams.has("sel"));
      return;
    case "EXPLORE_NEGATION":
      await page.getByRole("button", { name: "Explore ¬P" }).click();
      await page.waitForURL((url) => url.searchParams.get("flip") === "1");
      return;
    case "RETURN":
      await page.getByRole("button", { name: "Return to comparison" }).click();
      await page.waitForURL((url) => !url.searchParams.has("flip"));
      return;
    case "RESET":
      await page.getByRole("button", { name: "Reset view" }).click();
      await page.waitForURL((url) => !url.searchParams.has("sel") && !url.searchParams.has("flip"));
      return;
    case "RELOAD":
      await page.reload();
      return;
  }
}

for (const story of forestPaths()) {
  test(`FOREST-1: ${story.name}`, async () => {
    const page = await browser.newPage({ viewport: { width: 1360, height: 900 } });
    const errors: string[] = [];
    page.on("pageerror", (error) => errors.push(error.message));
    try {
      await page.goto(new URL(`${basePath}/forest/`, testOrigin ?? server!.url).toString());
      await assertState(page, "overview");
      for (const step of story.steps) {
        await perform(page, step.event);
        await assertState(page, step.state);
      }
      expect(errors).toEqual([]);
    } finally {
      await page.close();
    }
  }, 90000);
}
