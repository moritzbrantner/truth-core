# Koons's 2022 Fourth Way reconstruction

Primary witness: `KOONS-FOURTH-WAY-RECONSTRUCTION-2022-FULL-ITEM`, the
author-linked RSS item for [A Further Reconstruction of the Fourth
Way](https://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way),
published 23 January 2022. No claim or Lean formalization is added here.

## Reading returned for interpretation review

Steps 1–5 concern possible things and a **possible** maximum. Step 2 already
assumes comparison with such a possible standard; it is not a proof of an
actual maximum from bare gradation. Step 4 transfers maximal value to maximal
existence. Steps 6–13 import a necessary being **or plurality**, possible
universal causation in each world, a weak cause–effect degree bound, and
cross-world invariance of a necessary being's degree. The resulting
all-world maximum is conditional on that different modal/causal background.

The causal bound in step 7 is non-strict; it is not the repository's
unrestricted strict cause-more-such premise. A maximum relative to a world's
inhabitants and maximum possible existence also require separate treatment.
Plurality, transworld identity, domains and degree comparison are not silently
resolved by the post. Its closing concern is redundancy of the initial block,
not the uniqueness problem described in issue #345. No uniqueness conclusion
or direct discharge of `STMT-GRADES-HAVE-A-MAXIMUM` is warranted here.

## Witness and extraction boundary

The canonical HTML post is readable, but repeated fixed-User-Agent source
fetches changed their raw bytes. Comparing two responses isolated the change
to Cloudflare's per-request `r`/`t` script parameters; the selected post text
had the same SHA256. These responses were **not** normalized or admitted as a
stable source witness.

The page's actual RSS anchor is `/4/feed`; the adjacent `rel=alternate` link
has an empty `href`. Four normal source-tool fetches of
`https://robkoons.net/4/feed` gave identical response bytes:
`61854f98b4887ae9c5cbdea88f9fd1a83a4f1a318a0412dc6e058629ee1d9047`.
The existing `web_snapshot`/`raw_text` extractor preserves the UTF-8 XML
verbatim, including its CDATA, and materialization verifies those bytes.
The existing HTML heading/element selectors do not read this CDATA; no new
extractor was added.

The consulted item is uniquely identified by title, publication timestamp
`Sun, 23 Jan 2022 22:09:24 GMT`, and GUID/canonical link
`http://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way`.
Read its complete `content:encoded`, all thirteen numbered steps and both
closing paragraphs, from the **materialized** XML. Local XML/HTML decoding was
only a reading aid derived from that verified file; it did not replace the
snapshot, text hash or source-evidence extractor. The shorter RSS
`description` is not used as the argument witness.

Reproduction:

```bash
python3 scripts/source_evidence.py materialize KOONS-FOURTH-WAY-RECONSTRUCTION-2022-FULL-ITEM
```

No source text or feed bytes are committed. The feed can change in future;
without a matching fixed archive fallback this witness remains fragile.

## Rejected access approaches

- Canonical post URL: readable in this session, so issue #345's reported
  404 is no longer the present access state. The category URL
  `/old-blog-2021-22/category/fourth-way` returned 404 to browsing despite
  indexed results. Search snippets were orientation only.
- `www` and HTTP versions of the post redirect to the same volatile HTML.
  Its HTML advertises no print endpoint.
- Guessed `/1/feed`, `/old-blog-2021-22/1/feed` and
  `/old-blog-2021-22/rss.xml` failed. The author-linked `/4/feed` succeeded;
  `/old-blog-2021-22/feed` also served a feed but had a different channel
  publication timestamp and is not the pinned URL.
- HTTPS Wayback CDX and availability requests reset; HTTP availability
  returned 403. A request under the fixed path
  `https://web.archive.org/web/20260330150135id_/https://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way`
  also reset. This was an access probe, **not** a verified capture locator.
  The Arquivo.pt version-history query for the canonical URL reported zero
  captures. No archive timestamp or fallback hash is invented.
- A guessed `robkoons.weebly.com` version returned 404. No bibliographic
  fallback is needed or justified while a legitimate byte-pinned primary feed
  is available.

## Consequence boundary and next target

The current degree fork fixes one nonmodal contrast profile and strict causal
ascent. This reading instead motivates testing a modal weak-bound profile;
substituting one for the other would change premises. Compare the two blocks
under explicit world/domain/identity/degree semantics before adding attributed
claims or a bridge. Reuse existing statement identities only if their types
and meanings coincide. The witnessed unbounded branch has not been refuted by
this source reading, and no root premise closes.

## Validation

At source checkpoint `7aba445b78225b151b33ed4d584517cdc589a7d8`, offline source
and corpus checks passed. The normal
`source_evidence.py verify --base HEAD^ --head HEAD` command refetched and
verified the one newly added RSS passage with hash `61854f98b488`; the other
288 passages received offline checks only in that run. This verifies the
consulted feed bytes, not the argument or its interpretation.
