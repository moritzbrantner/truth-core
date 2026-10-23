/**
 * Derived proposition graph for the /graph page (#161).
 *
 * This is a view over the typed corpus records, never a canonical model
 * (docs/corpus-model.md, "Composition and visualization"). Statements and
 * inference applications are separate node kinds, so a logical step is always
 * premises → inference → conclusion (invariant 10). Relations stay a distinct,
 * non-inferential edge kind.
 *
 * Status follows the rules of `python3 scripts/corpus.py frontier` (#156/#159),
 * computed here so the page works whether or not that command and its optional
 * schema (`self_evident`, `alternative_to`, `refutes`, `attacks`) exist yet.
 */

export const DEFAULT_ROOT_STATEMENT_ID = "STMT-CATHOLICISM-TRUE";

/**
 * Stage conclusions of the root skeleton (#156, #159: CATHOLICISM-SKELETON).
 * A statement carries `stage:N` when stage N's conclusion rests on it. Entries
 * whose statement does not exist yet are ignored.
 */
export const STAGE_CONCLUSIONS: ReadonlyArray<{ stage: number; statementId: string }> = [
  { stage: 1, statementId: "STMT-GOD-EXISTS" },
  { stage: 2, statementId: "STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES" },
  { stage: 3, statementId: "STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE" },
  { stage: 4, statementId: "STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE" },
  { stage: 5, statementId: "STMT-CHRIST-FOUNDED-VISIBLE-CHURCH" },
  { stage: 6, statementId: "STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH" },
];

export type GraphStatus =
  | "proved"
  | "transcription"
  | "self-evident"
  | "defended"
  | "alternative"
  | "objection"
  | "open"
  | "derived"
  | "source-only";

export const GRAPH_STATUSES: ReadonlyArray<{ id: GraphStatus; label: string; description: string }> = [
  { id: "proved", label: "Proved", description: "Conclusion of an argument with a verified result." },
  {
    id: "transcription",
    label: "Transcription only",
    description:
      "Conclusion only of results whose proof applies one premise (invariant 16 heuristic); verified, but not progress.",
  },
  { id: "self-evident", label: "Self-evident", description: "Marked self_evident with a sourced justification." },
  { id: "defended", label: "Alternatives refuted", description: "Every recorded alternative is refuted by a verified argument." },
  { id: "alternative", label: "Alternative", description: "Recorded as an alternative to another statement." },
  { id: "objection", label: "Objection", description: "Recorded as an objection attacking another statement." },
  { id: "open", label: "Open premise", description: "Premise of an argument that is not proved, self-evident or defended: the frontier." },
  { id: "derived", label: "Intermediate step", description: "Output of an inference step that is not an argument conclusion with a result." },
  { id: "source-only", label: "Source reading only", description: "Stated by a source; no argument uses it yet." },
];

export type CorpusStatementInput = {
  id: string;
  paraphrase: string;
  lean_declaration?: string;
  self_evident?: { justification_ids: string[] };
};

export type CorpusClaimInput = {
  id: string;
  statement_id: string;
  source_id: string;
  locator: string;
  interpretation: string;
  interpretation_of?: string;
  interpretation_group?: string;
  passage_id?: string;
};

export type CorpusSourceInput = { id: string; author: string; work: string };

export type CorpusInferenceInput = {
  id: string;
  input_statement_ids: string[];
  output_statement_id: string;
  rule: string;
  meaning: string;
  assumption_statement_ids?: string[];
  discharged_statement_ids?: string[];
};

export type CorpusArgumentInput = {
  id: string;
  premise_statement_ids: string[];
  conclusion_statement_id: string;
  inference_ids: string[];
  meaning: string;
};

export type CorpusResultInput = { id: string; argument_id: string };

export type CorpusRelationInput = {
  id: string;
  subject_kind: string;
  subject_id: string;
  predicate: string;
  object_kind: string;
  object_id: string;
  basis?: string;
};

export type PropositionGraphInput = {
  statements: CorpusStatementInput[];
  claims: CorpusClaimInput[];
  sources: CorpusSourceInput[];
  inferences: CorpusInferenceInput[];
  arguments: CorpusArgumentInput[];
  results: CorpusResultInput[];
  relations: CorpusRelationInput[];
  /** Result IDs flagged by the transcription heuristic (see lean-transcription.ts). */
  transcriptionResultIds: string[];
};

export type GraphClaim = {
  id: string;
  sourceId: string;
  passageId?: string;
  locator: string;
  interpretation: string;
  reading?: string;
  interpretationOf?: string;
};

export type GraphStatement = {
  id: string;
  paraphrase: string;
  leanDeclaration?: string;
  namespace?: string;
  status: GraphStatus;
  /** Open premise by the corpus.py frontier rule. */
  frontier: boolean;
  /** Refuted by an argument with a verified result (`refutes`). */
  refuted: boolean;
  selfEvidentJustification: string[];
  tags: string[];
  claims: GraphClaim[];
  sourceIds: string[];
  premiseOf: string[];
  conclusionOf: string[];
  verifyingResultIds: string[];
  /** Arguments reached by repeatedly following the arguments that use it as a premise. */
  transitiveDependentArguments: number;
  stages: number[];
  clusters: Record<ClusterMode, string>;
};

export type GraphInference = {
  id: string;
  inputs: string[];
  assumptions: string[];
  discharged: string[];
  output: string;
  rule: string;
  meaning: string;
  argumentIds: string[];
};

export type GraphArgument = {
  id: string;
  meaning: string;
  premises: string[];
  conclusion: string;
  inferenceIds: string[];
  resultIds: string[];
  transcriptionResultIds: string[];
};

export type GraphRelation = {
  id: string;
  predicate: string;
  subject: string;
  object: string;
  basis?: string;
};

export type ClusterMode = "passage" | "source" | "namespace";

export type PropositionGraph = {
  statements: GraphStatement[];
  inferences: GraphInference[];
  arguments: GraphArgument[];
  relations: GraphRelation[];
  sources: CorpusSourceInput[];
  /** `STMT-CATHOLICISM-TRUE` when present, otherwise the verified conclusion resting on the most statements. */
  defaultTarget: string | null;
  rootPresent: boolean;
};

function push<K, V>(map: Map<K, V[]>, key: K, value: V) {
  const entries = map.get(key);
  if (entries) {
    entries.push(value);
  } else {
    map.set(key, [value]);
  }
}

export function leanNamespace(declaration: string | undefined) {
  if (!declaration || !declaration.includes(".")) {
    return undefined;
  }
  return declaration.split(".").slice(0, -1).join(".");
}

/** Reading label of a claim that takes part in an interpretation pair or group. */
function readingLabel(claim: CorpusClaimInput, interpretationTargets: Set<string>) {
  if (!claim.interpretation_of && !claim.interpretation_group && !interpretationTargets.has(claim.id)) {
    return undefined;
  }
  const suffix = /-([A-Z])$/.exec(claim.id)?.[1];
  if (suffix) {
    return suffix;
  }
  return claim.interpretation_of ? "alternative" : "base";
}

/** Statements a statement rests on, through the inferences that output it (inclusive). */
export function restsOn(start: string, producers: Map<string, Array<{ inputs: string[] }>>): Set<string> {
  const seen = new Set([start]);
  const queue = [start];
  while (queue.length) {
    const current = queue.shift() as string;
    for (const inference of producers.get(current) ?? []) {
      for (const input of inference.inputs) {
        if (!seen.has(input)) {
          seen.add(input);
          queue.push(input);
        }
      }
    }
  }
  return seen;
}

export function buildPropositionGraph(input: PropositionGraphInput): PropositionGraph {
  const statementIds = new Set(input.statements.map((statement) => statement.id));
  const sourceById = new Map(input.sources.map((source) => [source.id, source]));
  const argumentById = new Map(input.arguments.map((argument) => [argument.id, argument]));
  const transcription = new Set(input.transcriptionResultIds);

  const resultsByArgument = new Map<string, string[]>();
  for (const result of input.results) {
    push(resultsByArgument, result.argument_id, result.id);
  }
  const verifiedArguments = new Set(resultsByArgument.keys());

  const premiseOf = new Map<string, string[]>();
  const conclusionOf = new Map<string, string[]>();
  for (const argument of input.arguments) {
    for (const premise of new Set(argument.premise_statement_ids)) {
      push(premiseOf, premise, argument.id);
    }
    push(conclusionOf, argument.conclusion_statement_id, argument.id);
  }

  const argumentsByInference = new Map<string, string[]>();
  for (const argument of input.arguments) {
    for (const inferenceId of argument.inference_ids) {
      push(argumentsByInference, inferenceId, argument.id);
    }
  }
  const producers = new Map<string, Array<{ inputs: string[] }>>();
  const usedInferenceOutputs = new Set<string>();
  for (const inference of input.inferences) {
    push(producers, inference.output_statement_id, {
      inputs: [...inference.input_statement_ids, ...(inference.assumption_statement_ids ?? [])],
    });
    if (argumentsByInference.has(inference.id)) {
      usedInferenceOutputs.add(inference.output_statement_id);
    }
  }

  // Premise-program relations (#156); all optional.
  const alternatives = new Map<string, string[]>();
  const alternativeSubjects = new Set<string>();
  const objectionSubjects = new Set<string>();
  const refuted = new Set<string>();
  const relations: GraphRelation[] = [];
  for (const relation of input.relations) {
    if (relation.predicate === "alternative_to") {
      push(alternatives, relation.object_id, relation.subject_id);
      alternativeSubjects.add(relation.subject_id);
    } else if (relation.predicate === "refutes" && verifiedArguments.has(relation.subject_id)) {
      refuted.add(relation.object_id);
    } else if (relation.predicate === "attacks" && relation.subject_kind === "statement") {
      objectionSubjects.add(relation.subject_id);
    }
    if (
      relation.subject_kind === "statement" &&
      relation.object_kind === "statement" &&
      statementIds.has(relation.subject_id) &&
      statementIds.has(relation.object_id)
    ) {
      relations.push({
        id: relation.id,
        predicate: relation.predicate,
        subject: relation.subject_id,
        object: relation.object_id,
        basis: relation.basis,
      });
    }
  }

  // Transitive argument dependents, as in corpus.py frontier's upward walk.
  function transitiveDependents(statementId: string) {
    const seenArguments = new Set<string>();
    const seenStatements = new Set([statementId]);
    const queue = [statementId];
    while (queue.length) {
      const current = queue.shift() as string;
      for (const argumentId of premiseOf.get(current) ?? []) {
        seenArguments.add(argumentId);
        const conclusion = argumentById.get(argumentId)?.conclusion_statement_id;
        if (conclusion && !seenStatements.has(conclusion)) {
          seenStatements.add(conclusion);
          queue.push(conclusion);
        }
      }
    }
    return seenArguments.size;
  }

  const stagesByStatement = new Map<string, number[]>();
  for (const { stage, statementId } of STAGE_CONCLUSIONS) {
    if (!statementIds.has(statementId)) {
      continue;
    }
    for (const id of restsOn(statementId, producers)) {
      push(stagesByStatement, id, stage);
    }
  }

  const interpretationTargets = new Set(
    input.claims.flatMap((claim) => (claim.interpretation_of ? [claim.interpretation_of] : [])),
  );
  const claimsByStatement = new Map<string, GraphClaim[]>();
  for (const claim of [...input.claims].sort((left, right) => left.id.localeCompare(right.id))) {
    push(claimsByStatement, claim.statement_id, {
      id: claim.id,
      sourceId: claim.source_id,
      passageId: claim.passage_id,
      locator: claim.locator,
      interpretation: claim.interpretation,
      reading: readingLabel(claim, interpretationTargets),
      interpretationOf: claim.interpretation_of,
    });
  }

  const statements = input.statements.map((statement): GraphStatement => {
    const id = statement.id;
    const verifying = (conclusionOf.get(id) ?? []).flatMap((argumentId) => resultsByArgument.get(argumentId) ?? []);
    const recordedAlternatives = alternatives.get(id) ?? [];
    const defended = recordedAlternatives.length > 0 && recordedAlternatives.every((alt) => refuted.has(alt));
    const selfEvident = statement.self_evident !== undefined && statement.self_evident !== null;
    const frontier = premiseOf.has(id) && verifying.length === 0 && !selfEvident && !defended;

    let status: GraphStatus;
    if (verifying.length) {
      status = verifying.every((resultId) => transcription.has(resultId)) ? "transcription" : "proved";
    } else if (selfEvident) {
      status = "self-evident";
    } else if (defended) {
      status = "defended";
    } else if (alternativeSubjects.has(id)) {
      status = "alternative";
    } else if (objectionSubjects.has(id)) {
      status = "objection";
    } else if (frontier) {
      status = "open";
    } else if (usedInferenceOutputs.has(id)) {
      status = "derived";
    } else {
      status = "source-only";
    }

    const claims = claimsByStatement.get(id) ?? [];
    const sourceIds = [...new Set(claims.map((claim) => claim.sourceId))].sort();
    const namespace = leanNamespace(statement.lean_declaration);
    const stages = [...new Set(stagesByStatement.get(id) ?? [])].sort((a, b) => a - b);

    const tags = new Set<string>([`status:${status}`]);
    if (frontier) tags.add("frontier");
    for (const sourceId of sourceIds) {
      tags.add(`source:${sourceId}`);
      const author = sourceById.get(sourceId)?.author;
      if (author) tags.add(`author:${author}`);
    }
    if (namespace) tags.add(`ns:${namespace}`);
    for (const stage of stages) tags.add(`stage:${stage}`);
    if (alternativeSubjects.has(id)) tags.add("role:alternative");
    if (objectionSubjects.has(id)) tags.add("role:objection");
    if (refuted.has(id)) tags.add("role:refuted");
    for (const claim of claims) {
      if (claim.reading) tags.add(`reading:${claim.reading}`);
    }

    const firstClaim = claims[0];
    const namespaceCluster = namespace ?? "(no Lean declaration)";
    return {
      id,
      paraphrase: statement.paraphrase,
      leanDeclaration: statement.lean_declaration,
      namespace,
      status,
      frontier,
      refuted: refuted.has(id),
      selfEvidentJustification: statement.self_evident?.justification_ids ?? [],
      tags: [...tags].sort(),
      claims,
      sourceIds,
      premiseOf: premiseOf.get(id) ?? [],
      conclusionOf: conclusionOf.get(id) ?? [],
      verifyingResultIds: verifying,
      transitiveDependentArguments: premiseOf.has(id) ? transitiveDependents(id) : 0,
      stages,
      clusters: {
        passage: firstClaim ? (firstClaim.passageId ?? firstClaim.sourceId) : `derived · ${namespaceCluster}`,
        source: firstClaim ? firstClaim.sourceId : `derived · ${namespaceCluster}`,
        namespace: namespaceCluster,
      },
    };
  });

  const inferences = input.inferences.map((inference) => ({
    id: inference.id,
    inputs: inference.input_statement_ids,
    assumptions: inference.assumption_statement_ids ?? [],
    discharged: inference.discharged_statement_ids ?? [],
    output: inference.output_statement_id,
    rule: inference.rule,
    meaning: inference.meaning,
    argumentIds: argumentsByInference.get(inference.id) ?? [],
  }));

  const graphArguments = input.arguments.map((argument) => {
    const resultIds = resultsByArgument.get(argument.id) ?? [];
    return {
      id: argument.id,
      meaning: argument.meaning,
      premises: argument.premise_statement_ids,
      conclusion: argument.conclusion_statement_id,
      inferenceIds: argument.inference_ids,
      resultIds,
      transcriptionResultIds: resultIds.filter((resultId) => transcription.has(resultId)),
    };
  });

  const rootPresent = statementIds.has(DEFAULT_ROOT_STATEMENT_ID);
  let defaultTarget: string | null = rootPresent ? DEFAULT_ROOT_STATEMENT_ID : null;
  if (!defaultTarget) {
    let best = 0;
    const conclusions = [...new Set(input.arguments.filter((a) => verifiedArguments.has(a.id)).map((a) => a.conclusion_statement_id))].sort();
    for (const conclusion of conclusions) {
      const size = restsOn(conclusion, producers).size;
      if (size > best) {
        best = size;
        defaultTarget = conclusion;
      }
    }
  }

  return {
    statements,
    inferences,
    arguments: graphArguments,
    relations,
    sources: input.sources.map((source) => ({ id: source.id, author: source.author, work: source.work })),
    defaultTarget,
    rootPresent,
  };
}
