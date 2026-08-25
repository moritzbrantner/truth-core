import type { Metadata } from "next";

import { SiteHeader } from "@/components/site-header";

import "@xyflow/react/dist/style.css";
import "./globals.css";

export const metadata: Metadata = {
  title: "Truth Core — Scholarly corpus explorer",
  description: "Source-derived philosophical claims and mechanically verified arguments.",
};

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return (
    <html lang="en" suppressHydrationWarning>
      <body className="min-h-screen antialiased">
        <SiteHeader />
        <main className="mx-auto max-w-6xl px-5 pb-16 pt-12 sm:px-8 sm:pt-16">{children}</main>
        <footer className="mx-auto max-w-6xl border-t border-[var(--line)] px-5 py-8 text-sm text-[var(--muted)] sm:px-8">
          Truth Core preserves the boundary between textual interpretation and formal verification.
        </footer>
      </body>
    </html>
  );
}
