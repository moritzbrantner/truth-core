/** This is a presentation contract for frontier --json; no closure rule lives here. */
export type NextStatement = {
  statement_id: string; paraphrase: string; established: boolean; status: string;
  depth: "bare" | "supported" | "stated" | null; lean_declaration?: string; definition_ids: string[];
};
export type NextDerivation = {
  argument_id: string; meaning: string; conclusion_statement_id: string;
  premise_statement_ids: string[]; missing_statement_ids: string[]; result_ids: string[];
  verified: boolean; transcription: boolean;
};
export type NextRefutation = {
  argument_id: string; statement_id: string; counted: boolean; verified: boolean;
  unestablished_premise_statement_ids: string[];
};
export type NextRival = NextStatement & {refuted: boolean; refutations: NextRefutation[]; consequences: NextDerivation[]};
export type NextRoute = {
  argument_id: string; cost: number; verified: boolean; transcription: boolean; designated: boolean;
  cheapest: boolean; open_premise_statement_ids: string[]; open_premise_depths: Record<string, string>;
};
export type NextLeaf = NextStatement & {
  on_cheapest_route: boolean; route_depths: Record<string, string>; rivals: NextRival[];
  derivations: NextDerivation[];
  floor: {owner_decision_required: boolean; marking: null | {basis: string; reasons: string[]}};
  definition_decisions: {kind: string; status: string; description: string; decision?: string}[];
  impact: {routes_improved: number; total_cost_drop: number; routes: {argument_id: string; before: number; after: number; drop: number}[]};
  defense: {recorded_rival_count: number; undefeated_statement_ids: string[]; coverage: string};
};
export type NextPair = {
  left_argument_id: string; right_argument_id: string; shared_statement_ids: string[]; overlap_count: number;
  left_failure_statement_ids: string[]; right_failure_statement_ids: string[]; certified: boolean; remaining: string[];
};
export type NextStepsReport = {
  root: NextStatement | null; root_known: boolean; settlement_rules: Record<string, string>; impact_scope: string;
  routes: NextRoute[]; cheapest_argument_id: string | null; leaves: NextLeaf[]; joint_settlements: NextPair[];
  owner_decisions: {statement_id: string; paraphrase: string; impact: NextLeaf["impact"]; actions: NextLeaf["definition_decisions"]}[];
  joint_settlement_schema_result_ids: string[];
  failure_modes: Record<string, {statement_id: string; failure: string; recorded_rivals: NextRival[]; negation_consequence_coverage: string}>;
  partitions: {result_id: string; theorem: string; target_statement_id: string; target_established: boolean;
    coverage_statement_id: string; missing_background_statement_ids: string[]; survival_result_id?: string;
    note: string; cases: {label: string; lean_declaration: string; statement_id?: string; refuted: boolean; refutation_scope: string; refutations: NextRefutation[]}[]}[];
  floor_register: (NextStatement & {basis: string; met: boolean; reasons: string[]; reaches_root: boolean;
    owner_approval?: {decision: string; note?: string}; rivals: NextRival[]; dependents: {arguments: string[]; statements: string[]}})[];
  dag: {statements: NextStatement[]; arguments: NextDerivation[]};
};
