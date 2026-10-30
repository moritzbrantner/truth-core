import { StrengthComparisons } from "@/components/strength-comparisons";
import { getStrengthComparisons } from "@/lib/strength-comparisons";

export default function ComparisonsPage() {
  return <article className="max-w-5xl">
    <p className="eyebrow">Registered comparisons</p>
    <h1 className="mt-4 font-serif text-4xl tracking-[-0.04em] sm:text-5xl">What does the stronger proposition add?</h1>
    <p className="mt-5 max-w-4xl text-lg leading-8 text-[var(--muted)]">Inspect a selected comparison, its background, its proposed extra requirement and the checked proof applications. Comparisons use the existing corpus results; this page performs no theorem search or all-pairs comparison.</p>
    <StrengthComparisons comparisons={getStrengthComparisons()} showEmpty />
  </article>;
}
