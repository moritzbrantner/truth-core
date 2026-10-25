import type { CorpusWebPassage } from "./corpus";

type Assert<T extends true> = T;
type Common = Omit<CorpusWebPassage, "html_selector" | "pdf_pages">;
type Html = Common & { html_selector: { heading: string } };
type Pdf = Common & { pdf_pages: { first: number; last: number } };
type Both = Html & Pdf;

/** Compile-time contract: HTML and PDF selectors are alternatives. */
export type WebSelectorContract = [
  Assert<Html extends CorpusWebPassage ? true : false>,
  Assert<Pdf extends CorpusWebPassage ? true : false>,
  Assert<Both extends CorpusWebPassage ? false : true>,
  Assert<Common extends CorpusWebPassage ? false : true>,
];
