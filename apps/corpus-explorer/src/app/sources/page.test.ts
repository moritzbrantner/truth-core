import { expect, test } from "bun:test";

import { getCorpus } from "@/lib/corpus";

import SourcesPage from "./page";

test("sources page does not reorder a shared production corpus", () => {
  const originalMode = process.env.NODE_ENV;
  try {
    process.env.NODE_ENV = "development";
    getCorpus(); // Invalidate any cached production snapshot from another test.
    process.env.NODE_ENV = "production";
    const originalOrder = getCorpus().sources.map((source) => source.id);

    SourcesPage();

    expect(getCorpus().sources.map((source) => source.id)).toEqual(originalOrder);
  } finally {
    if (originalMode === undefined) {
      delete process.env.NODE_ENV;
    } else {
      process.env.NODE_ENV = originalMode;
    }
  }
});
