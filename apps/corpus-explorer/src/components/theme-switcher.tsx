"use client";

import { useEffect, useSyncExternalStore } from "react";

type Theme = "system" | "light" | "dark";

const themes: Theme[] = ["system", "light", "dark"];

function applyTheme(theme: Theme) {
  document.documentElement.dataset.theme = theme;
}

function readTheme(): Theme {
  const storedTheme = window.localStorage.getItem("truth-core-theme");
  return storedTheme === "light" || storedTheme === "dark" || storedTheme === "system" ? storedTheme : "system";
}

function subscribeToTheme(callback: () => void) {
  window.addEventListener("storage", callback);
  window.addEventListener("truth-core-theme-change", callback);

  return () => {
    window.removeEventListener("storage", callback);
    window.removeEventListener("truth-core-theme-change", callback);
  };
}

export function ThemeSwitcher() {
  const theme = useSyncExternalStore<Theme>(subscribeToTheme, readTheme, () => "system");

  useEffect(() => {
    applyTheme(theme);
  }, [theme]);

  function selectTheme(nextTheme: Theme) {
    window.localStorage.setItem("truth-core-theme", nextTheme);
    window.dispatchEvent(new Event("truth-core-theme-change"));
  }

  return (
    <fieldset aria-label="Color theme" className="flex border border-[var(--line)] text-[0.66rem] font-semibold tracking-[0.1em] uppercase">
      <legend className="sr-only">Color theme</legend>
      {themes.map((option) => (
        <button
          aria-pressed={theme === option}
          className="border-r border-[var(--line)] px-2 py-1.5 last:border-r-0 hover:bg-[var(--callout)] aria-pressed:bg-[var(--ink)] aria-pressed:text-[var(--paper)]"
          key={option}
          onClick={() => selectTheme(option)}
          type="button"
        >
          {option}
        </button>
      ))}
    </fieldset>
  );
}
