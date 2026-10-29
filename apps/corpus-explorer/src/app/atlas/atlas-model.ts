import { selectedConfiguration } from "@/lib/configuration-selection";
import type { Corpus } from "@/lib/corpus";
import type { FrontierDepth, FrontierReport, RootRoute } from "@/lib/site-state";
import type { ConfigurationCore, VerifiedConfigurationCase } from "@/lib/verified-configurations";

/** Presentation data only. The corpus report owns closure and dependency semantics. */
export type AtlasPremise = {
  id: string;
  label: string;
  depth: FrontierDepth;
  rootReaching: boolean;
  objections: string[];
  dependentArguments: string[];
  dependentStatements: string[];
};

export type AtlasRoute = RootRoute & {
  label: string;
  bare: number;
  sourced: number;
  provedUnestablished: number;
};

export type AtlasModel = {
  root: string;
  premises: AtlasPremise[];
  routes: AtlasRoute[];
  labels: Record<string, string>;
  arguments: Record<string, string>;
  argumentTargets: Record<string, string>;
  establishedRoot: boolean;
};

export type AtlasTile = {
  id: "root-bare" | "root-sourced" | "other-bare" | "other-sourced";
  title: string;
  count: number;
  premises: AtlasPremise[];
  depth: FrontierDepth;
  rootReaching: boolean;
};

export type AtlasCore = ConfigurationCore & { key: string };

export type AtlasMosaicCell = {
  mask: number;
  statementIds: string[];
  status: "verified incompatible" | "model witnessed" | "unresolved";
  resultId: string | null;
  modelId: string | null;
  unresolvedReason: string | null;
};

export function buildAtlasModel(corpus: Corpus, report: FrontierReport): AtlasModel {
  const labels = Object.fromEntries(corpus.statements.map((statement) => [statement.id, statement.paraphrase]));
  const argumentsById = Object.fromEntries(corpus.arguments.map((argument) => [argument.id, argument.meaning]));
  const resultByArgument = new Map(corpus.results.map((result) => [result.argument_id, result.id]));
  const depths = new Map(report.items.map((item) => [item.statement_id, item.depth]));
  const roots = new Set(report.reaching_root_statements);
  return {
    root: report.root,
    premises: report.items.map((item) => {
      const dependents = report.premise_dependents[item.statement_id];
      return {
        id: item.statement_id,
        label: item.paraphrase,
        depth: item.depth,
        rootReaching: roots.has(item.statement_id),
        objections: item.objections,
        dependentArguments: dependents?.arguments ?? [],
        dependentStatements: dependents?.statements ?? [],
      };
    }),
    routes: report.routes.routes.map((route) => ({
      ...route,
      label: argumentsById[route.argument_id] ?? route.argument_id,
      bare: route.open_premise_statement_ids.filter((id) => depths.get(id) === "bare").length,
      sourced: route.open_premise_statement_ids.filter((id) => depths.get(id) === "sourced").length,
      provedUnestablished: route.proved_unestablished_statement_ids.length,
    })),
    labels,
    arguments: argumentsById,
    argumentTargets: Object.fromEntries(corpus.arguments.map((argument) => [argument.id,
      resultByArgument.has(argument.id) ? `/results/${resultByArgument.get(argument.id)}` : `/statements/${argument.conclusion_statement_id}`])),
    establishedRoot: report.established_statements.includes(report.root),
  };
}

/** Disjoint partitions: neither sourced/bare nor root-reachability is an epistemic score. */
export function frontierTiles(premises: readonly AtlasPremise[]): AtlasTile[] {
  const groups = [
    { id: "root-bare", title: "Root-reaching · bare", rootReaching: true, depth: "bare" },
    { id: "root-sourced", title: "Root-reaching · sourced", rootReaching: true, depth: "sourced" },
    { id: "other-bare", title: "Other · bare", rootReaching: false, depth: "bare" },
    { id: "other-sourced", title: "Other · sourced", rootReaching: false, depth: "sourced" },
  ] as const;
  return groups.map((group) => {
    const matching = premises.filter((premise) => premise.rootReaching === group.rootReaching && premise.depth === group.depth);
    return { ...group, count: matching.length, premises: matching };
  });
}

/** Deduplicate identical certificates repeated in named sets and canonical terminal families. */
export function certifiedCores(configuration: VerifiedConfigurationCase): AtlasCore[] {
  const reports = [
    ...configuration.configurations,
    ...configuration.assumption_space.nodes.filter((node) => node.kind === "terminal").map((node) => node.report),
  ];
  const unique = new Map<string, AtlasCore>();
  for (const selection of reports) {
    if (selection.status !== "verified incompatible") { continue; }
    for (const core of selection.incompatible_cores) {
      const key = `${[...core.statement_ids].sort().join("|")}::${[...core.result_ids].sort().join("|")}`;
      if (!unique.has(key)) { unique.set(key, { ...core, key }); }
    }
  }
  return [...unique.values()].sort((a, b) => a.statement_ids.length - b.statement_ids.length || a.key.localeCompare(b.key));
}

/** Enumerate the *producer-certified* decision tree; never classify configurations here. */
export function certifiedMosaic(configuration: VerifiedConfigurationCase): AtlasMosaicCell[] {
  const dimensionIds = configuration.assumption_space.statement_ids;
  return Array.from({ length: 2 ** dimensionIds.length }, (_, index) => {
    const mask = index ^ (index >> 1); // Gray order keeps adjacent cells one assumption apart.
    const statementIds = dimensionIds.filter((_, bit) => (mask & (1 << bit)) !== 0);
    const selection = selectedConfiguration(configuration.assumption_space, statementIds);
    if (!selection.terminal) { throw new Error(`Invalid certified configuration ${configuration.id}: ${selection.error}`); }
    const report = selection.terminal.report;
    return {
      mask,
      statementIds,
      status: report.status,
      resultId: report.incompatible_cores[0]?.result_id ?? null,
      modelId: report.model_ids[0] ?? null,
      unresolvedReason: report.unresolved_reason,
    };
  });
}

export function routeImpact(route: AtlasRoute, premiseId: string): boolean {
  return route.open_premise_statement_ids.includes(premiseId);
}
