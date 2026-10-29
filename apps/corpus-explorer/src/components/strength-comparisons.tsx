import Link from "next/link";
import type { StrengthComparison } from "@/lib/strength-comparisons";
import { Expression } from "@/components/proposition-structure";

const roles: Record<string, string> = {
  implication: "Implication · S → W",
  delta_forward: "Added requirement follows · S → D",
  reconstruction: "Reconstruction · W and D imply S",
  equivalence: "Exact factorization · S ↔ (W ∧ D)",
  converse: "Converse · W → S",
  allowed_cases: "Allowed cases · W ↔ (S ∨ R)",
  remainder_identity: "Remainder identity · R ↔ (W ∧ ¬ S)",
};

function Formula({ label, text, statementId }: { label: string; text: string; statementId?: string }) {
  return <div className="min-w-0 rounded border border-[var(--line)] p-3">
    <p className="eyebrow">{label}</p>
    <pre className="mt-2 whitespace-pre-wrap break-words font-mono text-sm leading-6">{text}</pre>
    {statementId ? <Link className="link-quiet mt-2 inline-block break-all text-xs" href={`/statements/${statementId}#structure`}>{statementId} · inspect structure →</Link> : null}
  </div>;
}

export function StrengthComparisons({ comparisons, showEmpty = false }: { comparisons: StrengthComparison[]; showEmpty?: boolean }) {
  if (!comparisons.length && !showEmpty) return null;
  return <section className="record-section min-w-0" id="strength-comparisons" aria-label="Certified strength comparisons">
    <p className="eyebrow">Certified strength comparisons</p>
    <p className="mt-3 text-sm leading-6 text-[var(--muted)]">These compare open propositions under the displayed background and shared parameters. Availability of both propositions elsewhere in the library is not evidence of substantive equivalence. No claim of a unique or minimal added requirement is made.</p>
    {!comparisons.length ? <p className="mt-3 text-sm" data-strength-unavailable>No current certified comparison report is available. This view infers no implication, equivalence or strictness from missing evidence.</p> : null}
    {comparisons.map((comparison) => <article className="mt-7 min-w-0 rounded border border-[var(--line)] p-4 sm:p-5" id={comparison.id} key={comparison.id} data-strength-comparison={comparison.id}>
      <div className="flex flex-wrap items-center gap-3">
        <h3 className="break-all font-mono text-xs">{comparison.id}</h3>
        <span className="eyebrow" data-strength-status>{comparison.comparison_status}</span>
      </div>
      <p className="mt-3 text-sm leading-6">{comparison.note}</p>
      <div className="mt-5" aria-label="Selected background">
        <h4 className="eyebrow">Background Γ</h4>
        {comparison.binding.formulas.background.length ? <ul className="mt-2 grid gap-2 text-sm leading-6">{comparison.binding.formulas.background.map((formula, index) => <li className="min-w-0" key={`${index}:${formula}`}>
          <code className="whitespace-pre-wrap break-words">{formula}</code>
          {comparison.background_statement_ids[index] ? <Link className="link-quiet ml-2 break-all text-xs" href={`/statements/${comparison.background_statement_ids[index]}`}>{comparison.background_statement_ids[index]}</Link> : null}
        </li>)}</ul> : <p className="mt-2 text-sm leading-6">No propositional background assumptions. The parameter types and typeclass laws below remain part of the certificate.</p>}
      </div>
      <div className="mt-4 grid min-w-0 gap-3" aria-label="Exact comparison formulas">
        <Formula label="S · stronger proposition" text={comparison.binding.formulas.stronger} statementId={comparison.stronger_statement_id} />
        <Formula label="W · weaker proposition" text={comparison.binding.formulas.weaker} statementId={comparison.weaker_statement_id} />
        <Formula label="D · named proposed extra requirement" text={comparison.binding.formulas.delta} statementId={comparison.delta_statement_id} />
      </div>
      <p className="mt-3 text-sm leading-6" data-delta-status>Factorization: <strong>{comparison.delta_status}</strong>. This proves S ↔ (W ∧ D) when certified. Informative explanation remains a reviewed interpretation; valid factorization alone does not certify explanatory usefulness (for example, padding S with True). The degeneracy check detects only definitional matches to S or W → S; passing it proves no semantic nonredundancy.</p>
      <p className="mt-2 text-xs leading-6 text-[var(--muted)]">{comparison.explanatory_status}</p>
      {comparison.explanatory_controls.length ? <div className="mt-4" aria-label="Explanatory controls">
        <h4 className="eyebrow">Explanatory controls · separate from comparison verdicts</h4>
        <ul className="mt-2 grid gap-3">{comparison.explanatory_controls.map((control) => <li className="text-xs leading-6" key={control.result_id}>
          <Link className="link-quiet break-all" href={`/results/${control.result_id}`}>{control.result_id} · control evidence →</Link>
          <p>{control.description}</p>
        </li>)}</ul>
      </div> : null}
      <div className="mt-5" aria-label="Additional allowed cases">
        <Formula label="R · proposed description of the extra allowed cases" text={comparison.binding.formulas.remainder} statementId={comparison.remainder_statement_id} />
        <p className="mt-2 text-sm" data-remainder-status>{comparison.remainder_status ?? "No named remainder decomposition is certified here."}</p>
        <p className="mt-2 text-xs leading-6 text-[var(--muted)]">The general disjunctive remainder is W ∧ ¬ S. A named allowed case needs its own checked identity and decomposition; it is distinct from the added requirement D. Classical or decidability dependencies remain in the proof and axiom evidence.</p>
      </div>
      <div className="mt-5" aria-label="Comparison proof obligations">
        <h4 className="eyebrow">Proof obligations and evidence</h4>
        <p className="mt-2 text-xs leading-6 text-[var(--muted)]">Complete theorem applications are bound by Lean definitional equality. Readable formulas alone do not certify a binding.</p>
        <ul className="mt-3 grid gap-3">{comparison.obligations.map((obligation) => <li className="min-w-0 border-l border-[var(--line)] pl-3" key={obligation.role} data-strength-role={obligation.role}>
          <p className="text-sm leading-6">{roles[obligation.role] ?? obligation.role} · proved</p>
          <Link className="link-quiet break-all text-xs" href={`/results/${obligation.result_id}`}>{obligation.result_id} · proof →</Link>
          <details className="mt-1 text-xs leading-6">
            <summary className="cursor-pointer">Inspect full binding</summary>
            <p className="break-all">Theorem: {obligation.theorem}</p><p className="break-all">Argument: {obligation.argument_id}</p>
            {obligation.theorem_application ? <><p className="mt-2">Complete theorem application</p><pre className="whitespace-pre-wrap break-words">{obligation.theorem_application}</pre></> : null}
            <p className="mt-2">Expected type</p><pre className="whitespace-pre-wrap break-words">{obligation.expected_type}</pre>
            <p className="mt-2">Bound theorem type</p><pre className="whitespace-pre-wrap break-words">{obligation.actual_type}</pre>
            <p className="mt-2">Actual axiom dependencies: {obligation.axioms ? obligation.axioms.join(", ") || "none" : "not included in this report"}.</p>
            {obligation.permitted_axioms ? <p>Permitted axiom list: {obligation.permitted_axioms.join(", ") || "none"}.</p> : null}
          </details>
        </li>)}</ul>
        <p className="mt-3 text-sm" data-converse-status>Converse: {comparison.converse_status}.</p>
        <p className="mt-2 text-xs leading-6 text-[var(--muted)]">Failure to find a converse is unresolved. A checked instance satisfying the same Γ with W ∧ ¬ S refutes the general converse under this comparison; it does not assert separation for every fixed domain or interpretation. Current examples use Type 0; the closed-setting restriction does not require universe zero.</p>
        {comparison.separator ? <div className="mt-3 rounded border border-[var(--line)] p-3 text-sm leading-6" data-strength-separator>
          <p className="eyebrow">Checked separating setting · Γ with W ∧ ¬ S</p>
          <p className="mt-2 break-all font-mono text-xs">{comparison.separator.setting}</p>
          {comparison.separator.application ? <pre className="mt-2 whitespace-pre-wrap break-words text-xs">{comparison.separator.explicit_application ?? comparison.separator.application}</pre> : null}
          <Link className="link-quiet break-all text-xs" href={`/results/${comparison.separator.result_id}`}>{comparison.separator.result_id} · separating proof →</Link>
          <p className="break-all text-xs">{comparison.separator.theorem}</p>
          {comparison.separator.actual_type ? <pre className="mt-2 whitespace-pre-wrap break-words text-xs">{comparison.separator.actual_type}</pre> : null}
          {comparison.separator.parameters?.map((parameter, index) => <p className="break-all text-xs" key={index}>{parameter.expression} : {parameter.type}</p>)}
          {comparison.separator.axioms ? <p className="text-xs">Actual axiom dependencies: {comparison.separator.axioms.join(", ") || "none"}.</p> : null}
        </div> : null}
      </div>
      <details className="mt-5 text-sm leading-6" aria-label="Comparison parameters and definitions">
        <summary className="cursor-pointer">Shared parameter bindings, definitions and laws</summary>
        <p className="mt-3 break-all font-mono text-xs">Specification: {comparison.comparison_spec}</p>
        {comparison.binding.application || comparison.binding.specification_application ? <pre className="mt-2 whitespace-pre-wrap break-words text-xs">{comparison.binding.explicit_application ?? comparison.binding.application ?? comparison.binding.specification_application}</pre> : null}
        {comparison.binding.universe_parameters?.length ? <p className="mt-2 text-xs">Universe parameters: {comparison.binding.universe_parameters.join(", ")}.</p> : null}
        <ul className="mt-3 grid gap-2">{comparison.binding.parameters.map((parameter, index) => <li className="min-w-0 text-xs" key={`${index}:${parameter.name}`}><code className="whitespace-pre-wrap break-words">{parameter.name} : {parameter.type}</code>{parameter.binder_info ? <span className="ml-2 text-[var(--muted)]">{parameter.binder_info}</span> : null}</li>)}</ul>
        {comparison.binding.field_bindings?.map((binding) => <div className="mt-3 min-w-0 text-xs" key={binding.role}>
          <p className="break-all">{binding.role} · {binding.declaration}</p><pre className="whitespace-pre-wrap break-words">{binding.explicit_application ?? binding.expression} : {binding.type}</pre><p>Expected application (shared parameter indices {binding.parameter_indices.join(", ")})</p><pre className="whitespace-pre-wrap break-words">{binding.expected_application}</pre>
        </div>)}
        {comparison.binding.structure?.map((declaration, index) => <details className="mt-3" key={declaration.declaration}>
          <summary className="cursor-pointer break-all text-xs">Inspect bound expression structure · {declaration.declaration}</summary>
          {declaration.type ? <Expression node={declaration.type} role="declaration type" scope={`strength:${comparison.id}:${index}`} /> : null}
          {declaration.expansion ? <Expression node={declaration.expansion} role="definition body" scope={`strength:${comparison.id}:${index}`} /> : null}
          <p className="mt-2 text-xs text-[var(--muted)]">{declaration.coverage}</p>
          {declaration.references?.filter((reference) => reference.fields?.length).map((reference) => <details className="mt-2 text-xs" key={reference.declaration}>
            <summary className="cursor-pointer break-all">Model/typeclass fields · {reference.declaration}</summary>
            {reference.fields?.map((field) => <p className="mt-2 break-all" key={field.declaration}>{field.is_law ? "Law" : "Field"} · {field.declaration}: {field.type}</p>)}
          </details>)}
        </details>)}
        {comparison.binding.references?.map((reference) => <details className="mt-3 text-xs" key={reference.declaration}>
          <summary className="cursor-pointer break-all">{reference.declaration}</summary><p className="break-all">{reference.type}</p>
          {reference.fields?.map((field) => <p className="mt-2 break-all" key={field.declaration}>{field.is_law ? "Law" : "Field"} · {field.declaration}: {field.type}</p>)}
        </details>)}
        {comparison.definitions.map((definition) => <details className="mt-3" key={definition.id}>
          <summary className="cursor-pointer">{definition.term}</summary><Link className="link-quiet text-xs" href={`/definitions/${definition.id}`}>{definition.id}</Link>
          <p className="mt-2">{definition.definition}</p>{definition.note ? <p className="mt-2 text-[var(--muted)]">{definition.note}</p> : null}
        </details>)}
        {comparison.disambiguations.map((disambiguation) => <details className="mt-3" key={disambiguation.id}><summary className="cursor-pointer">{disambiguation.term ?? disambiguation.id}</summary><Link className="link-quiet text-xs" href={`/definitions#${disambiguation.id}`}>{disambiguation.id}</Link><p className="mt-2">{disambiguation.resolution}</p></details>)}
      </details>
      <div className="mt-5 text-sm leading-6" aria-label="Remaining comparison obligations">
        <h4 className="eyebrow">Remaining obligations</h4>
        <p className="mt-2">{comparison.remaining_obligations.length ? comparison.remaining_obligations.map((role) => roles[role] ?? role).join("; ") : "None for the advertised comparison under this background."}</p>
        <p className="mt-2 text-xs text-[var(--muted)]">This comparison does not establish its open propositions or background assumptions. Premise weakening and conclusion strengthening are separate operations; proof-term usage does not show logical necessity.</p>
        <ul className="mt-2 grid gap-1 text-xs text-[var(--muted)]">{comparison.scope_notes.map((note) => <li key={note}>{note}</li>)}</ul>
      </div>
    </article>)}
  </section>;
}
