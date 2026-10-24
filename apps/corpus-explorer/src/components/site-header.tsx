import Link from "next/link";

import { ThemeSwitcher } from "@/components/theme-switcher";

const links = [
  { href: "/", label: "State" },
  { href: "/claims", label: "Claims" },
  { href: "/sources", label: "Sources" },
  { href: "/results", label: "Arguments" },
  { href: "/definitions", label: "Terms" },
  { href: "/graph", label: "Graph" },
  { href: "/modal", label: "Modal logic" },
  { href: "/candidates", label: "Research queue" },
];

export function SiteHeader() {
  return (
    <header className="border-b border-[var(--line)]">
      <div className="mx-auto flex max-w-6xl items-center justify-between gap-4 px-5 py-5 sm:px-8">
        <Link className="font-serif text-2xl tracking-[-0.04em] text-[var(--ink)]" href="/">
          truth core
        </Link>
        <nav aria-label="Primary" className="flex items-center gap-4 overflow-x-auto text-sm text-[var(--muted)] sm:gap-6">
          {links.map((link) => (
            <Link className="whitespace-nowrap transition hover:text-[var(--ink)]" href={link.href} key={link.href}>
              {link.label}
            </Link>
          ))}
        </nav>
        <ThemeSwitcher />
      </div>
    </header>
  );
}
