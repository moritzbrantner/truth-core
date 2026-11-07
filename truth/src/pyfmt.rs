//! Python string formatting the ported text views reproduce byte for byte:
//! `str()` of JSON values, `repr()` of string lists, `str.split()`,
//! `str.splitlines()` and Python slice bounds.

use serde_json::Value;

/// Python `str.isspace()` for one character.
pub fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\x1c'..='\x1f').contains(&c)
}

/// Python `" ".join(text.split())`.
pub fn collapse(text: &str) -> String {
    text.split(is_space)
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Python `text.rstrip()`.
pub fn rstrip(text: &str) -> &str {
    text.trim_end_matches(is_space)
}

/// The first `count` characters (Python `text[:count]`, count >= 0).
pub fn head(text: &str, count: usize) -> &str {
    match text.char_indices().nth(count) {
        Some((index, _)) => &text[..index],
        None => text,
    }
}

/// Python `str.splitlines()`.
pub fn splitlines(text: &str) -> Vec<&str> {
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
        if !breaks {
            continue;
        }
        lines.push(&text[start..index]);
        start = index + c.len_utf8();
        if c == '\r' && chars.peek().is_some_and(|(_, next)| *next == '\n') {
            chars.next();
            start += 1;
        }
    }
    if start < text.len() {
        lines.push(&text[start..]);
    }
    lines
}

/// Python `repr()` of a string.
pub fn repr_str(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::from(quote);
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c == '\x7f' => out.push_str(&format!("\\x{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}

/// Python `repr()` of a JSON-loaded value.
pub fn repr(value: &Value) -> String {
    match value {
        Value::String(text) => repr_str(text),
        Value::Array(items) => format!(
            "[{}]",
            items.iter().map(repr).collect::<Vec<_>>().join(", ")
        ),
        Value::Object(map) => format!(
            "{{{}}}",
            map.iter()
                .map(|(key, value)| format!("{}: {}", repr_str(key), repr(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        other => text(other),
    }
}

/// Python `str()` of a JSON-loaded value, as an f-string prints it.
pub fn text(value: &Value) -> String {
    match value {
        Value::Null => "None".into(),
        Value::Bool(true) => "True".into(),
        Value::Bool(false) => "False".into(),
        Value::String(text) => text.clone(),
        Value::Number(number) => number.to_string(),
        other => repr(other),
    }
}

/// Python truthiness of a JSON-loaded value.
pub fn truthy(value: Option<&Value>) -> bool {
    match value {
        None | Some(Value::Null) => false,
        Some(Value::Bool(value)) => *value,
        Some(Value::String(value)) => !value.is_empty(),
        Some(Value::Array(value)) => !value.is_empty(),
        Some(Value::Object(value)) => !value.is_empty(),
        Some(Value::Number(value)) => value.as_f64() != Some(0.0),
    }
}

/// The end index of Python `entries[:limit]` for `len` entries.
pub fn slice_end(len: usize, limit: i64) -> usize {
    if limit >= 0 {
        (limit as usize).min(len)
    } else {
        len.saturating_sub(limit.unsigned_abs() as usize)
    }
}

/// Python `_short`: collapse whitespace and cut to `width` characters with an ellipsis.
pub fn short(value: Option<&str>, width: usize) -> String {
    let text = collapse(value.unwrap_or_default());
    if text.chars().count() <= width {
        text
    } else {
        format!("{}…", rstrip(head(&text, width.saturating_sub(1))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn python_string_helpers() {
        assert_eq!(collapse(" a\t b\x1c c \n"), "a b c");
        assert_eq!(splitlines("a\r\nb\rc\n"), vec!["a", "b", "c"]);
        assert_eq!(splitlines("a\n\nb"), vec!["a", "", "b"]);
        assert_eq!(repr(&json!(["a", "it's"])), "['a', \"it's\"]");
        assert_eq!(text(&json!(null)), "None");
        assert_eq!(text(&json!(3)), "3");
        assert_eq!(slice_end(5, -2), 3);
        assert_eq!(slice_end(5, 8), 5);
        assert_eq!(short(Some("abcdef"), 4), "abc…");
        assert_eq!(short(Some("ab  c"), 4), "ab c");
    }
}
