//! Lean-text transcription heuristics (invariant 16, #391), ported from
//! `scripts/corpus.py` (`transcription_flags`, `assembly_of`,
//! `assembled_hypotheses` and their helpers).
//!
//! Only the two heuristics that make a result a transcription are ported:
//! a proof that is a single application of one hypothesis, and a proof that
//! only assembles hypotheses into a tuple. The goal-consequent and
//! opaque-atom heuristics only warn in Python and change no closure, so they
//! are not needed here. The checks read Lean source text; they are
//! deterministic heuristics, not proofs.

use std::{collections::HashSet, fs, path::Path};

const OPEN_BRACKETS: &str = "([{⟨";
const CLOSE_BRACKETS: &str = ")]}⟩";

/// The heuristic transcription kind of a proof, if any.
#[derive(Debug, PartialEq, Eq)]
pub enum Heuristic {
    SingleApplication,
    Assembly,
}

/// Python `\w` on `str`: Unicode alphanumerics and underscore.
fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

/// Python `" ".join(text.split())`.
fn normalize(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// `re.sub(r"/-.*?-/", " ", DOTALL)` then `re.sub(r"--[^\n]*", "")`.
pub fn strip_lean_comments(text: &str) -> String {
    let mut without_blocks = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("/-") {
        let Some(end) = rest[start + 2..].find("-/") else {
            break;
        };
        without_blocks.push_str(&rest[..start]);
        without_blocks.push(' ');
        rest = &rest[start + 2 + end + 2..];
    }
    without_blocks.push_str(rest);
    let mut output = String::with_capacity(without_blocks.len());
    let mut rest = without_blocks.as_str();
    while let Some(start) = rest.find("--") {
        output.push_str(&rest[..start]);
        rest = &rest[start..];
        rest = &rest[rest.find('\n').unwrap_or(rest.len())..];
    }
    output.push_str(rest);
    output
}

/// Python `split_top_level`: split at `separator` outside brackets. A
/// separator that is itself a bracket never splits (bracket handling wins).
pub fn split_top_level(text: &str, separator: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth: i64 = 0;
    let mut start = 0;
    let mut index = 0;
    while index < text.len() {
        let c = text[index..].chars().next().unwrap_or_default();
        if OPEN_BRACKETS.contains(c) {
            depth += 1;
        } else if CLOSE_BRACKETS.contains(c) {
            depth -= 1;
        } else if depth == 0 && text[index..].starts_with(separator) {
            parts.push(normalize(&text[start..index]));
            start = index + separator.len();
            index = start;
            continue;
        }
        index += c.len_utf8();
    }
    parts.push(normalize(&text[start..]));
    parts
}

/// Text up to the next line that starts with a non-whitespace character.
fn declaration_block(text: &str) -> &str {
    let mut offset = 0;
    while let Some(position) = text[offset..].find('\n') {
        let newline = offset + position;
        if text[newline + 1..]
            .chars()
            .next()
            .is_some_and(|c| !c.is_whitespace())
        {
            return &text[..newline];
        }
        offset = newline + 1;
    }
    text
}

/// Binder groups `(bracket, names, type)` and the remaining header.
fn binder_groups(header: &str) -> (Vec<(char, Vec<String>, String)>, String) {
    let mut groups = Vec::new();
    let mut rest = header.trim().to_owned();
    while let Some(first) = rest.chars().next().filter(|c| "({[".contains(*c)) {
        let mut depth = 0;
        let mut end = rest.char_indices().last().map_or(0, |(index, _)| index);
        for (index, c) in rest.char_indices() {
            if OPEN_BRACKETS.contains(c) {
                depth += 1;
            } else if CLOSE_BRACKETS.contains(c) {
                depth -= 1;
                if depth == 0 {
                    end = index;
                    break;
                }
            }
        }
        let inner = &rest[first.len_utf8()..end.max(first.len_utf8())];
        let (names, binder_type) = inner.split_once(':').unwrap_or((inner, ""));
        groups.push((
            first,
            names.split_whitespace().map(str::to_owned).collect(),
            normalize(binder_type),
        ));
        let after = end + rest[end..].chars().next().map_or(0, char::len_utf8);
        rest = rest[after..].trim().to_owned();
    }
    (groups, rest)
}

/// `LEAN_IDENT_RE.match` at the start: `[A-Za-z_][\w.']*`.
fn ident_prefix(text: &str) -> Option<&str> {
    let mut chars = text.char_indices();
    let (_, first) = chars.next()?;
    if !ident_start(first) {
        return None;
    }
    let end = chars
        .find(|(_, c)| !(is_word(*c) || *c == '.' || *c == '\''))
        .map_or(text.len(), |(index, _)| index);
    Some(&text[..end])
}

/// `LEAN_IDENT_RE.findall`.
fn find_identifiers(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    let mut index = 0;
    while index < text.len() {
        if let Some(ident) = ident_prefix(&text[index..]) {
            found.push(ident.to_owned());
            index += ident.len();
        } else {
            index += text[index..].chars().next().map_or(1, char::len_utf8);
        }
    }
    found
}

/// Whether `text` starts with `word` followed by a regex word boundary.
fn starts_with_word(text: &str, word: &str) -> bool {
    text.strip_prefix(word)
        .is_some_and(|rest| !rest.chars().next().is_some_and(is_word))
}

/// `[A-Za-z_][\w']*` matching the whole of `text`.
fn plain_ident(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(ident_start) && chars.all(|c| is_word(c) || c == '\'')
}

/// Python `str.splitlines()`.
fn split_lines(text: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let mut start = 0;
    let mut chars = text.char_indices().peekable();
    while let Some((index, c)) = chars.next() {
        let breaks = matches!(
            c,
            '\n' | '\r'
                | '\x0b'
                | '\x0c'
                | '\x1c'
                | '\x1d'
                | '\x1e'
                | '\u{85}'
                | '\u{2028}'
                | '\u{2029}'
        );
        if breaks {
            lines.push(&text[start..index]);
            start = index + c.len_utf8();
            if c == '\r' && chars.peek().is_some_and(|(_, next)| *next == '\n') {
                chars.next();
                start += 1;
            }
        }
    }
    if start < text.len() {
        lines.push(&text[start..]);
    }
    lines
}

/// `PROJECTION_RE`: a hypothesis name with optional projections.
fn projection_head(term: &str) -> Option<&str> {
    let (head, projections) = term.split_once('.').unwrap_or((term, ""));
    if !plain_ident(head) {
        return None;
    }
    if !term.contains('.') {
        return Some(head);
    }
    projections
        .split('.')
        .all(|segment| {
            matches!(segment, "left" | "right" | "mp" | "mpr")
                || (!segment.is_empty() && segment.chars().all(|c| c.is_ascii_digit()))
        })
        .then_some(head)
}

fn assembled_hypotheses(term: &str, names: &HashSet<String>) -> Option<Vec<String>> {
    let mut term = normalize(term);
    while term.starts_with('(') && term.ends_with(')') && term.len() >= 2 {
        let inner = &term[1..term.len() - 1];
        if split_top_level(inner, ")")[0] != inner.trim() {
            break;
        }
        term = inner.trim().to_owned();
    }
    if let Some(head) = projection_head(&term) {
        return names.contains(head).then(|| vec![head.to_owned()]);
    }
    let parts = if term.starts_with('⟨') && term.ends_with('⟩') && term.len() >= 6 {
        let inner = &term['⟨'.len_utf8()..term.len() - '⟩'.len_utf8()];
        if split_top_level(inner, "⟩")[0] != normalize(inner) {
            return None;
        }
        split_top_level(inner, ",")
    } else {
        split_top_level(term.strip_prefix("And.intro ")?, " ")
    };
    let mut found = Vec::new();
    for part in parts {
        found.extend(assembled_hypotheses(&part, names)?);
    }
    Some(found)
}

/// `obtain ⟨…⟩ := h` (greedy pattern), as `(pattern, source)`.
fn obtain_step(step: &str) -> Option<(&str, &str)> {
    let rest = step.strip_prefix("obtain")?;
    let trimmed = rest.trim_start();
    if trimmed.len() == rest.len() || !trimmed.starts_with('⟨') {
        return None;
    }
    // Greedy `⟨.*⟩`: the last closing bracket after which `\s*:=\s*ident$` holds.
    for (index, _) in trimmed
        .match_indices('⟩')
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
    {
        let end = index + '⟩'.len_utf8();
        let remainder = trimmed[end..].trim_start();
        if let Some(source) = remainder.strip_prefix(":=") {
            let source = source.trim_start();
            if plain_ident(source) && !trimmed[..end].contains('\n') {
                return Some((&trimmed[..end], source));
            }
        }
    }
    None
}

/// `rcases h with ⟨…⟩`, as `(pattern, source)`.
fn rcases_step(step: &str) -> Option<(&str, &str)> {
    let rest = step.strip_prefix("rcases")?;
    let trimmed = rest.trim_start();
    if trimmed.len() == rest.len() {
        return None;
    }
    let end = trimmed
        .find(|c: char| !(is_word(c) || c == '\''))
        .unwrap_or(trimmed.len());
    let source = &trimmed[..end];
    let after = &trimmed[end..];
    let after_trimmed = after.trim_start();
    if !plain_ident(source) || after_trimmed.len() == after.len() {
        return None;
    }
    let with = after_trimmed.strip_prefix("with")?;
    let pattern = with.trim_start();
    (pattern.len() < with.len()
        && pattern.starts_with('⟨')
        && pattern.ends_with('⟩')
        && !pattern.contains('\n'))
    .then_some((pattern, source))
}

fn assembly_of(applied: &[String], hypothesis_names: &HashSet<String>) -> Option<Vec<String>> {
    let mut names = hypothesis_names.clone();
    let mut steps: &[String] = applied;
    while let Some(first) = steps.first() {
        let Some((pattern, source)) = obtain_step(first).or_else(|| rcases_step(first)) else {
            break;
        };
        if !names.contains(source) {
            return None;
        }
        names.extend(find_identifiers(pattern));
        steps = &steps[1..];
    }
    let first = steps.first()?;
    if first == "constructor" && steps.len() >= 3 {
        let mut found = Vec::new();
        for step in &steps[1..] {
            let step = step
                .strip_prefix('·')
                .map_or(step.as_str(), str::trim_start);
            let rest = step.strip_prefix("exact")?;
            let term = rest.trim_start();
            if term.len() == rest.len() || term.is_empty() {
                return None;
            }
            found.extend(assembled_hypotheses(term, &names)?);
        }
        return Some(found);
    }
    if steps.len() != 1 {
        return None;
    }
    let mut term = first.as_str();
    for keyword in ["exact", "refine", "apply"] {
        if let Some(rest) = term.strip_prefix(keyword) {
            let trimmed = rest.trim_start();
            if trimmed.len() < rest.len() {
                term = trimmed;
            }
            break;
        }
    }
    assembled_hypotheses(term, &names).filter(|found| found.len() >= 2)
}

/// The heuristic kind of the theorem `name` in the Lean source `text`, as
/// Python `transcription_flags` derives `single_application_of` and
/// `assembly_of`.
pub fn classify_source(text: &str, name: &str) -> Option<Heuristic> {
    let text = strip_lean_comments(text);
    let mut block = None;
    let mut line_start = 0;
    for line in text.split_inclusive('\n') {
        if let Some(rest) = text[line_start..].strip_prefix("theorem") {
            let trimmed = rest.trim_start();
            if trimmed.len() < rest.len()
                && let Some(after) = trimmed.strip_prefix(name)
            {
                let before_word = name.chars().last().is_some_and(is_word);
                let after_word = after.chars().next().is_some_and(is_word);
                if !name.is_empty() && before_word != after_word {
                    let start = text.len() - after.len();
                    block = Some(declaration_block(&text[start..]));
                    break;
                }
            }
        }
        line_start += line.len();
    }
    let block = block?;
    let (header, proof) = block.split_once(":=").unwrap_or((block, ""));
    let (groups, _) = binder_groups(header);
    let hypothesis_names: HashSet<String> = groups
        .iter()
        .filter(|(bracket, _, _)| *bracket == '(')
        .flat_map(|(_, names, _)| names.iter().cloned())
        .collect();
    let proof = proof.trim();
    let raw_steps = if starts_with_word(proof, "by") {
        split_lines(proof).into_iter().map(str::to_owned).collect()
    } else {
        vec![normalize(proof)]
    };
    let mut steps: Vec<String> = raw_steps
        .iter()
        .map(|line| line.trim().to_owned())
        .filter(|line| !line.is_empty() && line != "by")
        .collect();
    if let Some(first) = steps.first_mut()
        && let Some(rest) = first.strip_prefix("by ")
    {
        *first = rest.trim().to_owned();
    }
    let applied: Vec<String> = steps
        .into_iter()
        .filter(|step| !(starts_with_word(step, "intro") || starts_with_word(step, "intros")))
        .collect();
    if let [step] = applied.as_slice() {
        let step = step.strip_prefix("exact ").unwrap_or(step).trim();
        if let Some(head) = ident_prefix(step) {
            let head = head.split('.').next().unwrap_or(head);
            if hypothesis_names.contains(head) {
                return Some(Heuristic::SingleApplication);
            }
        }
    }
    assembly_of(&applied, &hypothesis_names)
        .filter(|found| !found.is_empty())
        .map(|_| Heuristic::Assembly)
}

/// The heuristic kind of a result's theorem, read from its Solution module
/// under `root`; `None` when the file or theorem is missing.
pub fn classify_result(root: &Path, solution_module: &str, theorem: &str) -> Option<Heuristic> {
    let path = root.join(solution_module.replace('.', "/") + ".lean");
    if !path.is_file() {
        return None;
    }
    let text = fs::read_to_string(path).ok()?;
    classify_source(&text, theorem.rsplit('.').next().unwrap_or(theorem))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_application_and_assembly() {
        let single = "theorem t (P Q : Prop) (h : P → Q) (hp : P) : Q := by\n  exact h hp\n";
        assert_eq!(
            classify_source(single, "t"),
            Some(Heuristic::SingleApplication)
        );
        let assembly = "theorem t (a : A) (b : B) : A ∧ B := ⟨a, b⟩\n";
        assert_eq!(classify_source(assembly, "t"), Some(Heuristic::Assembly));
        let destructured =
            "theorem t (h : A ∧ B) : B ∧ A := by\n  obtain ⟨a, b⟩ := h\n  exact ⟨b, a⟩\n";
        assert_eq!(
            classify_source(destructured, "t"),
            Some(Heuristic::Assembly)
        );
        let constructor =
            "theorem t (a : A) (b : B) : A ∧ B := by\n  constructor\n  · exact a\n  · exact b\n";
        assert_eq!(classify_source(constructor, "t"), Some(Heuristic::Assembly));
        let real = "theorem t (n : Nat) : n + 0 = n := by\n  simp\n";
        assert_eq!(classify_source(real, "t"), None);
        // A commented-out theorem and a longer name are not the theorem.
        let commented = "/- theorem t (h : Q) : Q := h -/\ntheorem t2 (h : Q) : Q := h\n";
        assert_eq!(classify_source(commented, "t"), None);
    }

    #[test]
    fn helpers_follow_python() {
        assert_eq!(split_top_level("a, (b, c), d", ","), ["a", "(b, c)", "d"]);
        assert_eq!(split_top_level("a ⟩ b", "⟩"), ["a ⟩ b"]);
        assert_eq!(strip_lean_comments("x -- c\ny /- z -/ w"), "x \ny   w");
        assert_eq!(find_identifiers("⟨a, b.1, _⟩"), ["a", "b.1", "_"]);
        assert_eq!(split_lines("a\r\nb\n"), ["a", "b"]);
        assert_eq!(projection_head("h.left.2"), Some("h"));
        assert_eq!(projection_head("h.foo"), None);
    }
}
