type StatusMarkProps = {
  children: React.ReactNode;
  tone?: "ink" | "accent" | "muted";
};

const tones = {
  ink: "border-[var(--ink)] text-[var(--ink)]",
  accent: "border-[var(--accent)] text-[var(--accent)]",
  muted: "border-[var(--line-strong)] text-[var(--muted)]",
};

export function StatusMark({ children, tone = "ink" }: StatusMarkProps) {
  return (
    <span className={`inline-flex border px-2 py-1 text-[0.66rem] font-semibold tracking-[0.12em] uppercase ${tones[tone]}`}>
      {children}
    </span>
  );
}
