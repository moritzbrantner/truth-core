"use client";

import Link from "next/link";
import { useRouter, useSearchParams } from "next/navigation";

import type { ForestArgument, ForestModel, ForestStatement } from "@/lib/argument-forest";
import styles from "./forest.module.css";

type TreeProps = {
  model: ForestModel;
  id: string;
  selected: string;
  expanded: ReadonlySet<string>;
  onSelect: (id: string) => void;
  onToggle: (id: string) => void;
  depth?: number;
  ancestors?: readonly string[];
};

function excerpt(value: string, limit = 115) {
  if (value.length <= limit) { return value; }
  return value.slice(0, limit - 1).trimEnd() + "…";
}

function StatementBranch({
  model, id, selected, expanded, onSelect, onToggle, depth = 0, ancestors = [],
}: TreeProps) {
  const statement = model.statements[id];
  if (!statement) {
    return <p className={styles.missing}>This premise is outside the bounded map. Inspect its corpus record.</p>;
  }
  const repeated = ancestors.includes(id);
  const argumentsShown = statement.argumentIds
    .map((argumentId) => model.arguments[argumentId])
    .filter((argument): argument is ForestArgument => Boolean(argument));
  const canExpand = !repeated && depth < 2 && argumentsShown.length > 0;
  const isExpanded = canExpand && expanded.has(id);

  return <div className={styles.branch}>
    <div className={styles.statement} data-status={statement.status} data-selected={selected === id}>
      <button type="button" aria-pressed={selected === id} onClick={() => onSelect(id)}
        className={styles.statementSelect} aria-label={"Select proposition: " + statement.paraphrase}>
        <span className={styles.statementMarker} aria-hidden="true" />
        <span className={styles.statementText}>
          <span className={styles.statementTitle}>{excerpt(statement.paraphrase, depth ? 104 : 145)}</span>
          <span className={styles.statementMeta}>{statement.statusLabel}</span>
        </span>
      </button>
      {canExpand ? <button type="button" className={styles.expand}
        aria-label={(isExpanded ? "Collapse arguments for " : "Expand arguments for ") + statement.id}
        aria-expanded={isExpanded} onClick={() => onToggle(id)}>
        {isExpanded ? "−" : "+"}
      </button> : null}
    </div>
    {repeated ? <p className={styles.hint}>Shared proposition · shown elsewhere in this path</p> : null}
    {!repeated && statement.totalArguments > 0 && !argumentsShown.length ?
      <p className={styles.hint}>Further arguments are outside this overview. Focus this proposition to inspect its records.</p> : null}
    {isExpanded ? <div className={styles.supports}>
      <p className={styles.junction}>OR · {statement.totalArguments} recorded argument{statement.totalArguments === 1 ? "" : "s"} supporting this conclusion</p>
      <div className={styles.argumentColumns}>
        {argumentsShown.map((argument) => <section key={argument.id} className={styles.argument}>
          <div className={styles.argumentHeading}>
            <span>AND · {argument.premises.length} ordinary premise{argument.premises.length === 1 ? "" : "s"}</span>
            <span>{argument.resultIds.length ? (argument.transcriptionOnly ? "Transcription result" : "Result recorded") : "No result recorded"}</span>
          </div>
          <p className={styles.argumentMeaning}>{excerpt(argument.meaning, 160)}</p>
          {argument.premises.length ? <div className={styles.premises}>
            {argument.premises.slice(0, 3).map((premise) =>
              <StatementBranch key={premise} model={model} id={premise} selected={selected}
                expanded={expanded} onSelect={onSelect} onToggle={onToggle}
                depth={depth + 1} ancestors={[...ancestors, id]} />)}
            {argument.premises.length > 3 ? <p className={styles.hint}>
              +{argument.premises.length - 3} other required premise{argument.premises.length === 4 ? "" : "s"} — not omitted from the actual argument
            </p> : null}
          </div> : <p className={styles.hint}>No ordinary premises listed. Consult the result for any commitments or conditions.</p>}
          <div className={styles.argumentFooter}>
            <span className={styles.mono}>{excerpt(argument.id, 37)}</span>
            {argument.resultIds[0] ? <Link href={"/results/" + argument.resultIds[0]}>Inspect result</Link> : null}
          </div>
        </section>)}
      </div>
      {statement.totalArguments > argumentsShown.length ? <p className={styles.hint}>
        +{statement.totalArguments - argumentsShown.length} additional argument routes are collapsed in this overview.
      </p> : null}
    </div> : null}
  </div>;
}

function ConclusionTree({
  model, id, title, subtitle, selected, expanded, onSelect, onToggle,
}: TreeProps & { title: string; subtitle: string }) {
  return <section className={styles.treePanel} aria-label={title}>
    <div className={styles.panelHeading}><div><span className={styles.eyebrow}>{title}</span><p>{subtitle}</p></div></div>
    <StatementBranch model={model} id={id} selected={selected} expanded={expanded}
      onSelect={onSelect} onToggle={onToggle} />
  </section>;
}

function Counterfactual({
  statement, onCompare,
}: {
  statement: ForestStatement;
  onCompare: (id: string) => void;
}) {
  return <section className={styles.treePanel} aria-label="Hypothetical negation">
    <div className={styles.panelHeading}>
      <div><span className={styles.eyebrow}>Counterfactual branch</span><p>What changes if this proposition is denied?</p></div>
    </div>
    <div className={styles.hypothesis}>
      <span className={styles.hypothesisIcon}>¬P</span>
      <div><strong>Suppose the selected proposition is false</strong><p>{excerpt(statement.paraphrase, 165)}</p></div>
    </div>
    <div className={styles.counterBranches}>
      <section>
        <h3>Potentially affected support</h3>
        <strong className={styles.bigNumber}>{statement.transitiveDependentArguments}</strong>
        <p>Recorded downstream arguments. This is dependency reach, not a count of disproved conclusions.</p>
        {statement.directConsequences.length ? <ul className={styles.compactList}>
          {statement.directConsequences.map((child) => <li key={child.id}>
            <Link href={"/statements/" + child.id}>{excerpt(child.paraphrase, 88)}</Link>
          </li>)}
        </ul> : <p>No direct dependent conclusion is recorded.</p>}
        {statement.totalDirectConsequences > statement.directConsequences.length ?
          <p className={styles.hint}>+{statement.totalDirectConsequences - statement.directConsequences.length} more direct dependent conclusions</p> : null}
      </section>
      <section>
        <h3>Recorded rival links</h3>
        {statement.rivals.length ? <ul className={styles.compactList}>
          {statement.rivals.map((rival) => <li key={rival.id + rival.predicate}>
            <span className={styles.linkType}>{rival.predicate.replaceAll("_", " ")} · research relation</span>
            <button type="button" onClick={() => onCompare(rival.id)}>{excerpt(rival.paraphrase, 90)}</button>
          </li>)}
        </ul> : <p>No explicitly linked rival proposition in this map. Negating P does not itself certify another conclusion.</p>}
        {statement.totalRivals > statement.rivals.length ? <p className={styles.hint}>Additional research links omitted from the overview.</p> : null}
      </section>
    </div>
    <p className={styles.warning}>This branch is a hypothetical assumption, not a verified negation or a Lean result. Losing an argument does not prove its conclusion false.</p>
  </section>;
}

function Inspector({ statement, onFocus, onFlip, flipped }: {
  statement: ForestStatement;
  onFocus: (id: string) => void;
  onFlip: () => void;
  flipped: boolean;
}) {
  const search = new URLSearchParams({ view: "focus", node: statement.id, sel: statement.id });
  return <aside className={styles.inspector} aria-label="Selected proposition">
    <div className={styles.inspectorTop}>
      <div><span className={styles.eyebrow}>Selected proposition</span><span className={styles.mono}>{statement.id}</span></div>
      <span className={styles.statusPill} data-status={statement.status}>{statement.statusLabel}</span>
    </div>
    <p className={styles.fullParaphrase}>{statement.paraphrase}</p>
    <div className={styles.inspectorStats}>
      <div><strong>{statement.totalArguments}</strong><span>Recorded supporting arguments</span></div>
      <div><strong>{statement.transitiveDependentArguments}</strong><span>Downstream arguments</span></div>
      <div><strong>{statement.totalRivals}</strong><span>Recorded rival links</span></div>
    </div>
    <div className={styles.inspectorActions}>
      <button type="button" className={styles.primary} onClick={onFlip}>{flipped ? "Return to comparison" : "Explore ¬P"}</button>
      <button type="button" onClick={() => onFocus(statement.id)}>Make this the goal</button>
      <Link href={"/statements/" + statement.id}>Corpus evidence</Link>
      <Link href={"/graph?" + search.toString()}>Full proof network</Link>
    </div>
  </aside>;
}

export function ForestExplorer({ model }: { model: ForestModel }) {
  const params = useSearchParams();
  const router = useRouter();
  const goal = model.statements[params.get("goal") ?? ""] ? params.get("goal")! : model.defaultGoal;
  const compare = model.statements[params.get("compare") ?? ""] ? params.get("compare")! : model.defaultCompare;
  const selected = model.statements[params.get("sel") ?? ""] ? params.get("sel")! : goal;
  const flipped = params.get("flip") === "1";
  const selectedStatement = model.statements[selected];
  const expanded = new Set(params.has("open") ? params.getAll("open").filter((id) => model.statements[id]) : [goal, compare]);

  function change(patch: Record<string, string | null>) {
    const query = new URLSearchParams(params.toString());
    for (const [key, value] of Object.entries(patch)) {
      if (value === null) { query.delete(key); }
      else { query.set(key, value); }
    }
    router.replace("/forest?" + query.toString(), { scroll: false });
  }

  function toggle(id: string) {
    const next = new Set(expanded);
    if (next.has(id)) { next.delete(id); }
    else { next.add(id); }
    const query = new URLSearchParams(params.toString());
    query.delete("open");
    // Explicit empty expansion distinguishes collapse-all from the default view.
    if (!next.size) { query.append("open", "-"); }
    else { for (const entry of [...next].slice(0, 8)) { query.append("open", entry); } }
    router.replace("/forest?" + query.toString(), { scroll: false });
  }

  function chooseGoal(id: string) {
    change({ goal: id, compare: compare === id ? model.roots.find((root) => root.id !== id)?.id ?? id : compare,
      sel: id, flip: null, open: null });
  }

  if (!selectedStatement || !model.statements[goal]) {
    return <p>No argument records are available for this build.</p>;
  }

  return <div className={styles.explorer}>
    <div className={styles.toolbar}>
      <label>Conclusion to investigate
        <select value={goal} onChange={(event) => chooseGoal(event.target.value)}>
          {model.roots.map((root) => <option key={root.id} value={root.id}>{root.label}</option>)}
        </select>
      </label>
      <label>Compare against
        <select value={compare} onChange={(event) => change({ compare: event.target.value, flip: null, open: null })}>
          {model.roots.filter((root) => root.id !== goal).map((root) =>
            <option key={root.id} value={root.id}>{root.label}</option>)}
          {!model.roots.some((root) => root.id === compare && root.id !== goal) ?
            <option value={compare}>{excerpt(model.statements[compare]?.paraphrase ?? compare, 70)}</option> : null}
        </select>
      </label>
      <button type="button" className={styles.reset} onClick={() => router.replace("/forest", { scroll: false })}>Reset view</button>
    </div>
    <div className={styles.mapKey}>
      <span><i data-status="established" /> Established</span>
      <span><i data-status="conditional" /> Conditional</span>
      <span><i data-status="open" /> Open</span>
      <span><i data-status="refuted" /> Refuted</span>
      <span>OR = alternative arguments · AND = all required premises</span>
    </div>
    <div className={styles.forest}>
      <ConclusionTree model={model} id={goal} title="Primary conclusion"
        subtitle="Recorded arguments support their conclusions only given their premises."
        selected={selected} expanded={expanded} onSelect={(id) => change({ sel: id })}
        onToggle={toggle} />
      {flipped ? <Counterfactual statement={selectedStatement}
        onCompare={(id) => change({ compare: id, flip: null })} /> :
        <ConclusionTree model={model} id={compare} title="Compared conclusion"
          subtitle="A separate recorded claim; not automatically the negation of the primary goal."
          selected={selected} expanded={expanded} onSelect={(id) => change({ sel: id })}
          onToggle={toggle} />}
    </div>
    <Inspector statement={selectedStatement} flipped={flipped}
      onFocus={chooseGoal} onFlip={() => change({ flip: flipped ? null : "1" })} />
    <p className={styles.disclaimer}>Argument nodes are alternative recorded derivations (OR); every shown premise of an argument is jointly required (AND).
      This map intentionally limits visible branches. All claims of establishment, refutation and proof remain owned by the corpus and verifier,
      not by this visual layout. Research rival links never count as formal implications.</p>
  </div>;
}
