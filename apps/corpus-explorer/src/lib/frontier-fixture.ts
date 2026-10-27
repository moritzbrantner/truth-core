import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

import {
  buildPropositionGraph,
  type PropositionGraphInput,
} from "./proposition-graph";
import type { FrontierReport } from "./site-state";

/** A fixture corpus plus the results that the Lean heuristics would flag as transcriptions. */
export type GraphFixtureInput = PropositionGraphInput & { transcriptionResultIds: string[] };

/** Tests exercise Python's actual closure semantics, never a second JS solver. */
export function fixtureReport(input: GraphFixtureInput): FrontierReport {
  return JSON.parse(
    execFileSync(
      "python3",
      [
        "-c",
        `
import json, sys
sys.path.insert(0, 'scripts')
from corpus import frontier_report
x = json.load(sys.stdin)
flags = [dict(result_id=r['id'], argument_id=r['argument_id'], proof_steps=1,
 single_application_of='fixture', goal_consequent_premises=[])
 for r in x['results'] if r['id'] in x['transcriptionResultIds']]
print(json.dumps(frontier_report(x['statements'], x['arguments'], x['results'],
 x['relations'], root='ROOT', transcription=flags, claims=x['claims'], inferences=x['inferences'])))
`,
      ],
      {
        cwd: fileURLToPath(new URL("../../../../", import.meta.url)),
        input: JSON.stringify(input),
        encoding: "utf8",
      },
    ),
  ) as FrontierReport;
}

export function fixtureGraph(input: GraphFixtureInput) {
  return buildPropositionGraph(input, fixtureReport(input));
}
