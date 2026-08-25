export type ProjectionStatement = {
  id: string;
  paraphrase: string;
};

export type ProjectionInference = {
  id: string;
  input_statement_ids: string[];
  output_statement_id: string;
  rule: string;
  meaning: string;
};

export type ProjectionArgument = {
  id: string;
  premise_statement_ids: string[];
  conclusion_statement_id: string;
  inference_ids: string[];
  meaning: string;
};

export type ArgumentProjectionCorpus = {
  statements: ProjectionStatement[];
  inferences: ProjectionInference[];
  arguments: ProjectionArgument[];
  verified_argument_ids: string[];
};

export type ProjectedInferenceStep = {
  id: string;
  rule: string;
  meaning: string;
  inputs: ProjectionStatement[];
  output: ProjectionStatement;
};

export type ProjectedArgumentNode = {
  id: string;
  argumentId: string;
  meaning: string;
  premises: ProjectionStatement[];
  conclusion: ProjectionStatement;
  steps: ProjectedInferenceStep[];
  expanded: boolean;
  verified: boolean;
  depth: number;
};

export type ProjectedArgumentEdge = {
  id: string;
  source: string;
  target: string;
  statementId: string;
  cycle: boolean;
};

export type ArgumentProjection = {
  nodes: ProjectedArgumentNode[];
  edges: ProjectedArgumentEdge[];
};

function requiredStatement(statements: Map<string, ProjectionStatement>, statementId: string) {
  const statement = statements.get(statementId);
  if (!statement) {
    throw new Error(`Unknown statement in projection: ${statementId}`);
  }
  return statement;
}

export function projectArgumentComposition(
  corpus: ArgumentProjectionCorpus,
  rootArgumentId: string,
  expandedArgumentIds: ReadonlySet<string>,
): ArgumentProjection {
  const statementById = new Map(corpus.statements.map((statement) => [statement.id, statement]));
  const inferenceById = new Map(corpus.inferences.map((inference) => [inference.id, inference]));
  const argumentById = new Map(corpus.arguments.map((argument) => [argument.id, argument]));
  const verifiedArgumentIds = new Set(corpus.verified_argument_ids);
  const rootArgument = argumentById.get(rootArgumentId);

  if (!rootArgument) {
    throw new Error(`Unknown root argument: ${rootArgumentId}`);
  }

  const supportingArgumentsByStatement = new Map<string, ProjectionArgument[]>();
  for (const argument of corpus.arguments) {
    if (!verifiedArgumentIds.has(argument.id)) {
      continue;
    }
    const existing = supportingArgumentsByStatement.get(argument.conclusion_statement_id) ?? [];
    existing.push(argument);
    supportingArgumentsByStatement.set(argument.conclusion_statement_id, existing);
  }

  const nodeById = new Map<string, ProjectedArgumentNode>();
  const edgeById = new Map<string, ProjectedArgumentEdge>();
  const activePath = new Set<string>();
  const completed = new Set<string>();

  function ensureNode(argument: ProjectionArgument, depth: number) {
    const existing = nodeById.get(argument.id);
    if (existing) {
      existing.depth = Math.max(existing.depth, depth);
      return existing;
    }

    const premises = argument.premise_statement_ids.map((statementId) =>
      requiredStatement(statementById, statementId),
    );
    const conclusion = requiredStatement(statementById, argument.conclusion_statement_id);
    const steps = argument.inference_ids.map((inferenceId) => {
      const inference = inferenceById.get(inferenceId);
      if (!inference) {
        throw new Error(`Unknown inference in projection: ${inferenceId}`);
      }
      return {
        id: inference.id,
        rule: inference.rule,
        meaning: inference.meaning,
        inputs: inference.input_statement_ids.map((statementId) =>
          requiredStatement(statementById, statementId),
        ),
        output: requiredStatement(statementById, inference.output_statement_id),
      };
    });

    const node: ProjectedArgumentNode = {
      id: argument.id,
      argumentId: argument.id,
      meaning: argument.meaning,
      premises,
      conclusion,
      steps,
      expanded: expandedArgumentIds.has(argument.id),
      verified: verifiedArgumentIds.has(argument.id),
      depth,
    };
    nodeById.set(argument.id, node);
    return node;
  }

  function visit(argument: ProjectionArgument, depth: number) {
    ensureNode(argument, depth);

    if (completed.has(argument.id) || !expandedArgumentIds.has(argument.id)) {
      return;
    }

    activePath.add(argument.id);

    for (const premiseId of argument.premise_statement_ids) {
      const supporters = supportingArgumentsByStatement.get(premiseId) ?? [];
      for (const supporter of supporters) {
        if (supporter.id === argument.id) {
          continue;
        }

        const isCycle = activePath.has(supporter.id);
        ensureNode(supporter, depth + 1);
        const edgeId = `${supporter.id}->${argument.id}:${premiseId}`;
        edgeById.set(edgeId, {
          id: edgeId,
          source: supporter.id,
          target: argument.id,
          statementId: premiseId,
          cycle: isCycle,
        });

        if (!isCycle) {
          visit(supporter, depth + 1);
        }
      }
    }

    activePath.delete(argument.id);
    completed.add(argument.id);
  }

  visit(rootArgument, 0);

  return {
    nodes: [...nodeById.values()].sort((left, right) =>
      right.depth - left.depth || left.argumentId.localeCompare(right.argumentId),
    ),
    edges: [...edgeById.values()].sort((left, right) => left.id.localeCompare(right.id)),
  };
}
