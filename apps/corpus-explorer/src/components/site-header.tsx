import Link from "next/link";

import { ThemeSwitcher } from "@/components/theme-switcher";
import { DEFAULT_ROOT_STATEMENT_ID } from "@/lib/proposition-graph";

const links = [
  { href: "/", label: "Frontier" },
  { href: "/forest", label: "Forest" },
  { href: "/guide/classical-god", label: "Guide" },
  { href: "/atlas", label: "Atlas" },
  { href: "/state", label: "Case" },
  { href: "/next", label: "Next steps" },
  { href: `/statements/${DEFAULT_ROOT_STATEMENT_ID}`, label: "Root proposition" },
  { href: "/candidates", label: "Research" },
  { href: "/results", label: "Results" },
  { href: "/sources", label: "Sources" },
];

export function SiteHeader() {
  return (
    <header className="border-b border-[var(--line)]">
      <div className="mx-auto flex max-w-[96rem] items-center justify-between gap-4 px-5 py-4 sm:px-8">
        <Link className="font-serif text-2xl tracking-[-0.04em] text-[var(--ink)]" href="/">
          truth core
        </Link>
        <nav aria-label="Primary" className="flex min-w-0 flex-1 items-center gap-4 overflow-x-auto text-sm text-[var(--muted)] sm:gap-6">
          {links.map((link) => (
            <Link className="whitespace-nowrap transition hover:text-[var(--ink)]" href={link.href} key={link.href}>
              {link.label}
            </Link>
          ))}
        </nav>
        <details className="site-reference-menu">
          <summary>Reference</summary>
          <div>
            <Link href="/claims">Source readings</Link>
            <Link href="/definitions">Definitions</Link>
            <Link href="/comparisons">Proposition strength</Link>
            <Link href="/skeleton">Skeleton details</Link>
            <Link href="/modal">Modal logic lab</Link>
            <Link href="/objective-truth">Truth pilot</Link>
          </div>
        </details>
        <ThemeSwitcher />
      </div>
    </header>
  );
}
