import {
  claimsForResult,
  findResult,
  findStatement,
  type Corpus,
  type CorpusClaim,
  type CorpusResult,
  type CorpusStatement,
} from "@/lib/corpus";
import { legacyUuid } from "@/lib/corpus-ids";
import type { FrontierReport, RootRoute } from "@/lib/site-state";

export const GOD_ROOT_ID = legacyUuid("statement", "STMT-NECESSARY-CLASSICAL-GOD-ROOT");
export const ASSEMBLY_RESULT_ID = legacyUuid("result", "CLASSICAL-GOD-FROM-POSITIVE-ROOT");

/** Only the editorial explanation is authored here. Results, edges and statuses come from the corpus. */
const steps = [
  {
    resultId: legacyUuid("result", "DIRECT-ESSE-ROOT-PERFECTION"),
    title: "A necessary root, with a qualified kind of perfection",
    explanation: "Under a particular account of concrete grounding, modal necessity and degrees of being, a single selected actual root is necessary at accessible worlds and maximal in the supplied 'act of being' respect. It is perfect in a formal-or-eminent sense: not yet morally perfect, omniscient, or God.",
    next: "The root still needs accounts of goodness, composition, intellect and will before it can carry more familiar divine descriptions.",
    focus: [
      { id: legacyUuid("statement", "STMT-WHOLE-ROSTER-NOT-TRAPPED"), label: "The grounding network has a source", question: "Why must the whole actual network escape being trapped in dependence?" },
      { id: legacyUuid("statement", "STMT-GRADES-TO-MAXIMUM-AT-BEING"), label: "Degrees point to a maximum", question: "Do degrees of being guarantee a maximum in the specified sense?" },
      { id: legacyUuid("statement", "STMT-PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE"), label: "A cause carries its effects' perfections", question: "In what sense does a cause possess the perfections it explains?" },
    ],
  },
  {
    resultId: legacyUuid("result", "PERFECT-ROOT-POSITIVE-INTELLECT-WILL"),
    title: "That same root acquires further attributes",
    explanation: "Supplying the previous perfect-root result, existing rules add causal goodness, simplicity, represented essence/being identity, firstness, immateriality, intellect and will. The formal result retains the original individual rather than combining properties of different witnesses.",
    next: "Calling this individual 'God', establishing infinity and eternity, and packaging the full classical attribute set still require additional commitments.",
    focus: [
      { id: legacyUuid("statement", "STMT-COMPOSITE-HAS-A-UNITING-CAUSE"), label: "Composition calls for a uniting cause", question: "Is a composite necessarily caused by something distinct in the required sense?" },
      { id: legacyUuid("statement", "STMT-IMMATERIAL-IS-INTELLECTUAL"), label: "Immateriality supports intellect", question: "Does the selected notion of immateriality warrant the intellect predicate?" },
      { id: legacyUuid("statement", "STMT-WILL-FOLLOWS-INTELLECT"), label: "Will follows intellect", question: "What links the proved structural description to a genuine will?" },
    ],
  },
  {
    resultId: ASSEMBLY_RESULT_ID,
    title: "The conditional classical-God conclusion",
    explanation: "The final assembly keeps that individual fixed while applying further rules for pure act, infinity, eternity, God-naming and uniqueness. It bundles nine specified attributes and a separate classical-attributes predicate. The registered proof is an assembly, not an independent defense of those rules.",
    next: "Even if this conclusion follows from the stated inputs, we still need reasons to apply the causal, modal, naming, intellectual and attribute-sufficiency assumptions to reality.",
    focus: [
      { id: legacyUuid("statement", "STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE"), label: "Why call this 'God'?", question: "The name is applied through an explicit nominal definition, not inferred just from necessity." },
      { id: legacyUuid("statement", "STMT-SUBSISTENT-BEING-IS-INFINITE"), label: "Why infinite?", question: "A separate reading connects identity of essence and being to infinity." },
      { id: legacyUuid("statement", "STMT-CLASSICAL-ATTRIBUTES-SUFFICE"), label: "Why do these attributes suffice?", question: "A further premise identifies the nine predicates with the classical attribute field." },
    ],
  },
];

export type GuidePremise = { statement: CorpusStatement; onOpenRoute: boolean; fromPreviousStep: boolean };
export type GuideFocus = { statement: CorpusStatement; label: string; question: string };
export type GuideStage = {
  result: CorpusResult;
  conclusion: CorpusStatement;
  title: string;
  explanation: string;
  next: string;
  premises: GuidePremise[];
  focus: GuideFocus[];
  sourceClaims: CorpusClaim[];
  transcription: boolean;
};
export type GodWalkthrough = {
  stages: GuideStage[];
  route: RootRoute;
  rootRoutes: RootRoute[];
  openLeaves: CorpusStatement[];
};

function required<T>(value: T | undefined, id: string): T {
  if (!value) {
    throw new Error(`Missing canonical walkthrough record: ${id}`);
  }
  return value;
}

/** Project the named route without reimplementing proof closure or argument traversal. */
export function buildGodWalkthrough(corpus: Corpus, report: FrontierReport): GodWalkthrough {
  if (report.root !== GOD_ROOT_ID || report.routes.root !== GOD_ROOT_ID) {
    throw new Error(`Expected the frontier report for ${GOD_ROOT_ID}`);
  }
  const assembly = required(findResult(corpus, ASSEMBLY_RESULT_ID), ASSEMBLY_RESULT_ID);
  const route = required(report.routes.routes.find((entry) => entry.argument_id === assembly.argument_id), assembly.argument_id);
  const openIds = new Set(route.open_premise_statement_ids);
  const openLeaves = route.open_premise_statement_ids.map((id) => required(findStatement(corpus, id), id));

  const stages = steps.map((step, index): GuideStage => {
    const result = required(findResult(corpus, step.resultId), step.resultId);
    const conclusion = required(findStatement(corpus, result.argument.conclusion_statement_id), result.argument.conclusion_statement_id);
    const previousConclusion = index > 0
      ? required(findResult(corpus, steps[index - 1].resultId), steps[index - 1].resultId).argument.conclusion_statement_id
      : null;
    if (previousConclusion && !result.argument.premise_statement_ids.includes(previousConclusion)) {
      throw new Error(`${step.resultId} no longer consumes ${previousConclusion}`);
    }
    const premises = result.argument.premise_statement_ids.map((id): GuidePremise => ({
      statement: required(findStatement(corpus, id), id),
      onOpenRoute: openIds.has(id),
      fromPreviousStep: id === previousConclusion,
    }));
    const focus = step.focus.map((item): GuideFocus => {
      if (!result.argument.premise_statement_ids.includes(item.id)) {
        throw new Error(`${item.id} is no longer an input to ${result.id}`);
      }
      return { statement: required(findStatement(corpus, item.id), item.id), label: item.label, question: item.question };
    });
    const allClaims = claimsForResult(corpus, result.id);
    const focusClaims = allClaims.filter((claim) => focus.some((item) => item.statement.id === claim.statement_id));
    return {
      result,
      conclusion,
      title: step.title,
      explanation: step.explanation,
      next: step.next,
      premises,
      focus,
      sourceClaims: (focusClaims.length ? focusClaims : allClaims).slice(0, 3),
      transcription: Boolean(report.transcription_results[result.id]),
    };
  });
  if (stages.at(-1)?.conclusion.id !== GOD_ROOT_ID || route.cost !== openLeaves.length) {
    throw new Error("Walkthrough route does not match its registered conclusion and open-leaf cost");
  }
  return { stages, route, rootRoutes: report.routes.routes, openLeaves };
}
