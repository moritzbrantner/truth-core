import type { GraphFixtureInput } from "./frontier-fixture";

const statement = (id: string, extra = {}) => ({ id, paraphrase: `${id} paraphrase`, lean_declaration: `TruthCore.Test.${id}`, ...extra });

/** Small corpus covering every status, used by the graph tests. */
export const fixture: GraphFixtureInput = {
  statements: [
    statement("P1"),
    statement("P2"),
    statement("C"),
    statement("ROOT"),
    statement("SE", { self_evident: { justification_ids: ["CL-SE"] } }),
    statement("ALT"),
    statement("DEF"),
    statement("OBJ"),
    statement("LONE"),
    statement("T"),
    statement("TC"),
    statement("TOP"),
    statement("NALT"),
  ],
  claims: [
    { id: "CL-P1-A", statement_id: "P1", source_id: "SRC", locator: "1a", interpretation: "Reading A.", interpretation_group: "G", passage_id: "SRC-1" },
    { id: "CL-P1-B", statement_id: "P2", source_id: "SRC", locator: "1a", interpretation: "Reading B.", interpretation_of: "CL-P1-A", passage_id: "SRC-1" },
    { id: "CL-SE", statement_id: "SE", source_id: "SRC2", locator: "2b", interpretation: "Per se nota.", passage_id: "SRC2-2" },
    { id: "CL-LONE", statement_id: "LONE", source_id: "SRC", locator: "3c", interpretation: "Just said.", passage_id: "SRC-3" },
  ],
  sources: [
    { id: "SRC", author: "Aristotle", work: "Physics" },
    { id: "SRC2", author: "Thomas Aquinas", work: "Summa theologiae" },
  ],
  inferences: [
    { id: "I1", input_statement_ids: ["P1", "P2"], output_statement_id: "C", rule: "modus_ponens", meaning: "C." },
    { id: "I2", input_statement_ids: ["C", "SE", "DEF"], output_statement_id: "ROOT", rule: "conjunction_introduction", meaning: "Root." },
    { id: "I3", input_statement_ids: ["ALT"], output_statement_id: "OBJ", rule: "modus_tollens", meaning: "Refutation." },
    { id: "I4", input_statement_ids: ["T"], output_statement_id: "TC", rule: "modus_ponens", meaning: "Transcribed." },
    { id: "I5", input_statement_ids: ["TC"], output_statement_id: "TOP", rule: "modus_ponens", meaning: "Uses a transcription." },
    { id: "I6", input_statement_ids: [], output_statement_id: "NALT", rule: "reductio", meaning: "ALT is contradictory." },
  ],
  arguments: [
    { id: "A1", premise_statement_ids: ["P1", "P2"], conclusion_statement_id: "C", inference_ids: ["I1"], meaning: "C follows." },
    { id: "A2", premise_statement_ids: ["C", "SE", "DEF"], conclusion_statement_id: "ROOT", inference_ids: ["I2"], meaning: "Root follows." },
    { id: "A3", premise_statement_ids: ["ALT"], conclusion_statement_id: "OBJ", inference_ids: ["I3"], meaning: "Refutes ALT." },
    { id: "A4", premise_statement_ids: ["T"], conclusion_statement_id: "TC", inference_ids: ["I4"], meaning: "Transcribed." },
    { id: "A5", premise_statement_ids: ["TC"], conclusion_statement_id: "TOP", inference_ids: ["I5"], meaning: "Rests on a transcription." },
    { id: "A6", premise_statement_ids: [], conclusion_statement_id: "NALT", inference_ids: ["I6"], meaning: "Refutes ALT without premises." },
  ],
  results: [
    { id: "R1", argument_id: "A1" },
    { id: "R2", argument_id: "A2" },
    { id: "R4", argument_id: "A4" },
    { id: "R6", argument_id: "A6" },
  ],
  relations: [
    { id: "REL1", subject_kind: "statement", subject_id: "ALT", predicate: "alternative_to", object_kind: "statement", object_id: "DEF" },
    { id: "REL2", subject_kind: "argument", subject_id: "A6", predicate: "refutes", object_kind: "statement", object_id: "ALT" },
    { id: "REL3", subject_kind: "statement", subject_id: "OBJ", predicate: "attacks", object_kind: "statement", object_id: "C" },
    { id: "REL4", subject_kind: "claim", subject_id: "CL-LONE", predicate: "supports", object_kind: "statement", object_id: "T", note: "Source evidence, not a proof step." },
  ],
  transcriptionResultIds: ["R4"],
};
