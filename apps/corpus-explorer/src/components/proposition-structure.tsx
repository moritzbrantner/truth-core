import Link from "next/link";
import type { ExpressionNode, StructureReport } from "@/lib/proposition-structure";

/** Presentation only: ordered edges remain ordered, including implicit arguments. */
export function Expression({ node, role, scope }: { node: ExpressionNode; role: string; scope: string }) {
  const address = `${scope}:${node.id}`;
  return (
    <details className="mt-2 min-w-0 border-l border-[var(--line)] pl-3" id={address} data-expression-kind={node.kind}>
      <summary className="cursor-pointer break-words text-sm leading-6">
        <span className="eyebrow">{role} · {node.kind}</span>{" "}
        {node.binder_name ? <strong>{node.binder_name} </strong> : null}
        <code className="break-all">{node.text}</code>
        {node.coverage !== "complete" ? <span className="ml-2 text-[var(--accent)]">{node.coverage}</span> : null}
      </summary>
      <div className="mt-2 min-w-0 text-xs leading-6 text-[var(--muted)]">
        <p className="break-all">Address: <a className="link-quiet" href={`#${address}`}>{node.id}</a></p>
        <p className="break-all">Type: <code>{node.type}</code></p>
        <p>Coverage: {node.coverage}</p>
        {node.binder_info ? <p>Parameter binding: {node.binder_info}</p> : null}
        {node.binding ? <p className="break-all">Bound by: <a className="link-quiet" href={`#${scope}:${node.binding}`}>{node.binding}</a></p> : null}
        {node.declaration ? <p className="break-all">Declaration: {node.declaration}</p> : null}
        {node.boundary ? <p>Boundary: {node.boundary}{node.unfold_available ? " · project body available when selected below" : ""}</p> : null}
      </div>
      {node.children.map((child) => <Expression node={child.node} role={child.role} scope={scope} key={child.node.id} />)}
    </details>
  );
}

export function PropositionStructure({ report }: { report?: StructureReport }) {
  const expressionAnchors = new Map<string, string>();
  report?.declarations.forEach((decl, index) => {
    const scope = `${report.statement_id}:${report.revision.input_digest}:${index}`;
    const visit = (node: ExpressionNode) => {
      expressionAnchors.set(node.id, `${scope}:${node.id}`);
      node.children.forEach(({ node: child }) => visit(child));
    };
    if (decl.type) visit(decl.type);
    if (decl.expansion) visit(decl.expansion);
  });
  return (
    <section className="record-section min-w-0" id="structure" aria-label="Proposition structure">
      <p className="eyebrow">Proposition structure</p>
      <p className="mt-3 text-sm leading-6 text-[var(--muted)]">Expand the elaborated Lean expression to inspect its ordered arguments, parameter bindings and named boundaries. This derived view changes no statement identity or frontier status. A disjunction displays its alternatives; it selects no branch.</p>
      {!report ? <p className="mt-3 text-sm" data-structure-unavailable>Structure extraction is outside the current published slice, or its build input is unavailable. The source declaration above and existing corpus records remain available.</p> : (
        <details className="mt-4" data-structure-inspector>
          <summary className="cursor-pointer font-serif text-xl">Inspect expression and definitions</summary>
          <p className="mt-3 break-all font-mono text-xs text-[var(--muted)]">Revision {report.revision.head} · inputs {report.revision.input_digest}</p>
          <p className="mt-3 text-xs leading-6 text-[var(--muted)]">Addresses are scoped to this statement and its recorded input revision. Expansion exposes stored project definition bodies and preserves named library boundaries; it is not a proof or a Boolean normalization.</p>
          <div className="mt-6" aria-label="Expression structure">
            {report.declarations.map((decl, index) => {
              const scope = `${report.statement_id}:${report.revision.input_digest}:${index}`;
              return <div className="mt-6 min-w-0" key={decl.declaration}>
                <h3 className="break-all font-mono text-sm">{decl.declaration}</h3>
                {decl.error ? <p className="mt-2 text-sm">Extraction limitation: {decl.error}</p> : null}
                {decl.coverage ? <p className="mt-2 text-xs text-[var(--muted)]">{decl.coverage}</p> : null}
                {decl.type ? <Expression node={decl.type} role="declaration type" scope={scope} /> : null}
                {decl.expansion ? <details className="mt-3 rounded border border-[var(--line)] p-3" data-definition-expansion>
                  <summary className="cursor-pointer text-sm">Expand selected project definition · {decl.declaration.split(".").at(-1)}</summary>
                  <Expression node={decl.expansion} role="definition body" scope={scope} />
                </details> : <p className="mt-2 text-xs text-[var(--muted)]">Named boundary retained. {decl.unfold_status}</p>}
                {decl.references?.length ? <details className="mt-3">
                  <summary className="cursor-pointer text-sm">Referenced definitions, models and law fields ({decl.references.length})</summary>
                  <ul className="mt-2 grid gap-3">
                    {decl.references.map((reference) => <li className="min-w-0 text-xs leading-6" key={reference.declaration}>
                      <p className="break-all font-mono">{reference.declaration} · {reference.kind}</p>
                      <p className="break-all text-[var(--muted)]">{reference.type ?? "Type unavailable: unresolved reference"}</p>
                      {reference.fields?.map((field) => <p className="mt-1 break-all border-l border-[var(--line)] pl-3" key={field.declaration}><span className="eyebrow">{field.is_law ? "Law field" : "Data field"}</span> <code>{field.declaration}</code>: {field.type}</p>)}
                    </li>)}
                  </ul>
                </details> : null}
              </div>;
            })}
          </div>
          <div className="mt-7" aria-label="Semantic interpretation">
            <h3 className="eyebrow">Semantic interpretation · corpus records</h3>
            {[...report.semantic_links.definitions, ...report.semantic_links.disambiguations].map((record) => <details className="mt-3 text-sm leading-6" key={record.id}>
              <summary className="cursor-pointer">{record.term ?? record.id}</summary>
              <Link className="link-quiet break-all font-mono text-xs" href={record.id.startsWith("DISAMB-") ? `/definitions#${record.id}` : `/definitions/${record.id}`}>{record.id}</Link>
              <p className="mt-2">{record.definition ?? record.resolution}</p>
              {record.note ? <p className="mt-2 text-[var(--muted)]">{record.note}</p> : null}
              <p className="mt-2 break-all text-xs text-[var(--muted)]">Expression references: {record.expression_ids?.length ? record.expression_ids.map((id, index) => <span key={id}>{index ? ", " : ""}{expressionAnchors.has(id) ? <a className="link-quiet" href={`#${expressionAnchors.get(id)}`}>{id}</a> : id}</span>) : "contextual link; no exact declaration match"}</p>
            </details>)}
          </div>
          <div className="mt-7" aria-label="Proof support and bridge direction">
            <h3 className="eyebrow">Proof support and bridge direction</h3>
            <p className="mt-2 text-sm leading-6 text-[var(--muted)]">The following are corpus links, separate from definition expansion. A listed argument or open bridge does not establish equivalence.</p>
            {report.support.related_statements.map((statement) => <div className="mt-3 text-sm leading-6" key={statement.statement_id}>
              <Link className="link-quiet break-all" href={`/statements/${statement.statement_id}`}>{statement.statement_id}</Link>
              <p>{statement.paraphrase}</p><p className="text-xs text-[var(--muted)]">Status: {statement.frontier_status}</p>
            </div>)}
            {report.support.arguments.map((argument) => <div className="mt-3 text-xs leading-6" key={argument.id}>
              <p className="break-all">{argument.id}: {argument.premise_statement_ids.join(" ∧ ")} → {argument.conclusion_statement_id}</p>
              <p>{argument.meaning}</p>
              {report.support.results.filter((result) => result.argument_id === argument.id).map((result) => <Link className="link-quiet mr-3 break-all" href={`/results/${result.id}`} key={result.id}>{result.id}</Link>)}
            </div>)}
          </div>
          <div className="mt-7 text-sm leading-6" aria-label="Coverage limits">
            <h3 className="eyebrow">Coverage limits</h3>
            <ul className="mt-3 grid gap-2">{report.coverage_notes.map((note) => <li key={note}>{note}</li>)}</ul>
          </div>
        </details>
      )}
    </section>
  );
}
