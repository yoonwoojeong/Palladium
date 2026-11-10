//! Minimal JSON pull reader over `&[u8]`. See docs/DESIGN.md section 2.
//!
//! The caller walks containers with `obj_begin` / `obj_key` / `obj_more` and
//! `arr_begin` / `arr_more` (or the `each_key!` / `each_elem!` macros). Every
//! member value must be consumed by a typed reader or by `skip_value`.
//! Nothing allocates except `parse_string_into`, which writes into a
//! caller-owned buffer.

use std::fmt;

/// Maximum nesting depth accepted by `skip_value`.
pub const MAX_DEPTH: u32 = 512;

/// A syntax error at byte offset `pos` of the buffer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub pos: usize,
    pub msg: &'static str,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.msg, self.pos)
    }
}

impl std::error::Error for ParseError {}

type PResult<T> = Result<T, ParseError>;

/// A cursor over a JSON text. `pos` never exceeds `buf.len()`.
pub struct Cursor<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
}

/// Walks the members of the object at the cursor. The body receives each key
/// as `$key: &[u8]` and must consume the member's value.
macro_rules! each_key {
    ($c:expr, $key:ident => $body:expr) => {{
        if $c.obj_begin()? {
            loop {
                let $key: &[u8] = $c.obj_key()?;
                $body;
                if !$c.obj_more()? {
                    break;
                }
            }
        }
    }};
}

/// Walks the elements of the array at the cursor. The body must consume one element.
macro_rules! each_elem {
    ($c:expr, $body:block) => {{
        if $c.arr_begin()? {
            loop {
                $body;
                if !$c.arr_more()? {
                    break;
                }
            }
        }
    }};
}

pub(crate) use each_elem;
pub(crate) use each_key;

impl<'a> Cursor<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Cursor { buf, pos: 0 }
    }

    fn err<T>(&self, msg: &'static str) -> PResult<T> {
        Err(ParseError { pos: self.pos, msg })
    }

    /// The unread input.
    fn rest(&self) -> &'a [u8] {
        let buf: &'a [u8] = self.buf;
        buf.get(self.pos..).unwrap_or(&[])
    }

    /// Skips JSON whitespace.
    #[inline]
    pub fn skip_ws(&mut self) {
        while let Some(&b) = self.buf.get(self.pos) {
            if matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    /// Returns the next non-whitespace byte without consuming it.
    #[inline]
    pub fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.buf.get(self.pos).copied()
    }

    /// True when only whitespace remains.
    pub fn at_end(&mut self) -> bool {
        self.skip_ws();
        self.pos >= self.buf.len()
    }

    /// Consumes the byte `b` (after whitespace) or fails.
    pub fn expect(&mut self, b: u8) -> PResult<()> {
        self.skip_ws();
        if self.buf.get(self.pos) == Some(&b) {
            self.pos += 1;
            Ok(())
        } else {
            self.err("unexpected character")
        }
    }

    /// Parses a non-negative integer that fits in `u64`.
    pub fn parse_u64(&mut self) -> PResult<u64> {
        self.skip_ws();
        let start = self.pos;
        let mut v: u64 = 0;
        let mut i = start;
        let buf = self.buf;
        while i < buf.len() {
            let d = buf[i].wrapping_sub(b'0');
            if d > 9 {
                break;
            }
            v = match v.checked_mul(10).and_then(|x| x.checked_add(d as u64)) {
                Some(x) => x,
                None => {
                    self.pos = i;
                    return self.err("integer does not fit in u64");
                }
            };
            i += 1;
        }
        self.pos = i;
        if self.pos == start {
            return self.err("expected integer");
        }
        Ok(v)
    }

    /// Parses `true` or `false`.
    pub fn parse_bool(&mut self) -> PResult<bool> {
        self.skip_ws();
        let rest = self.rest();
        if rest.starts_with(b"true") {
            self.pos += 4;
            Ok(true)
        } else if rest.starts_with(b"false") {
            self.pos += 5;
            Ok(false)
        } else {
            self.err("expected boolean")
        }
    }

    /// Parses a string that contains no escape sequences and returns its raw
    /// bytes, borrowed from the input. Fails on escapes and control characters.
    pub fn parse_plain_string(&mut self) -> PResult<&'a [u8]> {
        self.skip_ws();
        if self.buf.get(self.pos) != Some(&b'"') {
            return self.err("expected string");
        }
        let buf: &'a [u8] = self.buf;
        let start = self.pos + 1;
        // Keys and names are short and almost always plain: one scan finds the end.
        match buf[start..].iter().position(|&b| b == b'"' || b == b'\\' || b < 0x20) {
            None => {
                self.pos = buf.len();
                self.err("unterminated string")
            }
            Some(r) => {
                let i = start + r;
                match buf[i] {
                    b'"' => {
                        self.pos = i + 1;
                        Ok(&buf[start..i])
                    }
                    b'\\' => {
                        self.pos = i;
                        self.err("escape sequence not allowed here")
                    }
                    _ => {
                        self.pos = i;
                        self.err("control character in string")
                    }
                }
            }
        }
    }

    /// Parses a string with full JSON decoding into UTF-8 bytes. `out` is
    /// cleared first. Lone surrogates decode to U+FFFD. Invalid UTF-8 in the
    /// input is an error.
    pub fn parse_string_into(&mut self, out: &mut Vec<u8>) -> PResult<()> {
        out.clear();
        self.skip_ws();
        if self.buf.get(self.pos) != Some(&b'"') {
            return self.err("expected string");
        }
        let buf: &'a [u8] = self.buf;
        self.pos += 1;
        loop {
            let start = self.pos;
            let mut i = start;
            while i < buf.len() {
                let b = buf[i];
                if b == b'"' || b == b'\\' {
                    break;
                }
                if b < 0x20 {
                    self.pos = i;
                    return self.err("control character in string");
                }
                i += 1;
            }
            if i >= buf.len() {
                self.pos = i;
                return self.err("unterminated string");
            }
            let run = &buf[start..i];
            if !run.is_ascii() && std::str::from_utf8(run).is_err() {
                self.pos = start;
                return self.err("invalid UTF-8 in string");
            }
            out.extend_from_slice(run);
            if buf[i] == b'"' {
                self.pos = i + 1;
                return Ok(());
            }
            // Escape sequence.
            self.pos = i + 1;
            let Some(&e) = buf.get(self.pos) else {
                return self.err("unterminated escape sequence");
            };
            self.pos += 1;
            match e {
                b'"' => out.push(b'"'),
                b'\\' => out.push(b'\\'),
                b'/' => out.push(b'/'),
                b'b' => out.push(0x08),
                b'f' => out.push(0x0c),
                b'n' => out.push(b'\n'),
                b'r' => out.push(b'\r'),
                b't' => out.push(b'\t'),
                b'u' => {
                    let ch = self.unicode_escape()?;
                    let mut tmp = [0u8; 4];
                    out.extend_from_slice(ch.encode_utf8(&mut tmp).as_bytes());
                }
                _ => return self.err("invalid escape sequence"),
            }
        }
    }

    fn hex4(&mut self) -> PResult<u32> {
        let mut v = 0u32;
        for _ in 0..4 {
            let Some(&b) = self.buf.get(self.pos) else {
                return self.err("truncated \\u escape");
            };
            let d = match b {
                b'0'..=b'9' => b - b'0',
                b'a'..=b'f' => b - b'a' + 10,
                b'A'..=b'F' => b - b'A' + 10,
                _ => return self.err("invalid hex digit in \\u escape"),
            };
            v = v * 16 + d as u32;
            self.pos += 1;
        }
        Ok(v)
    }

    /// Decodes the part of a `\u` escape after the `u`, including a following
    /// low surrogate escape when the first unit is a high surrogate.
    fn unicode_escape(&mut self) -> PResult<char> {
        const REPLACEMENT: char = '\u{FFFD}';
        let u = self.hex4()?;
        if (0xD800..0xDC00).contains(&u) {
            if self.buf.get(self.pos) == Some(&b'\\') && self.buf.get(self.pos + 1) == Some(&b'u') {
                let save = self.pos;
                self.pos += 2;
                let lo = self.hex4()?;
                if (0xDC00..0xE000).contains(&lo) {
                    let cp = 0x1_0000 + ((u - 0xD800) << 10) + (lo - 0xDC00);
                    return Ok(char::from_u32(cp).unwrap_or(REPLACEMENT));
                }
                // Not a pair: the high surrogate is lost, the next escape is read again.
                self.pos = save;
            }
            return Ok(REPLACEMENT);
        }
        if (0xDC00..0xE000).contains(&u) {
            return Ok(REPLACEMENT);
        }
        Ok(char::from_u32(u).unwrap_or(REPLACEMENT))
    }

    /// Begins an object (`{`). Returns false for `{}`, otherwise true; in the
    /// true case the caller reads a key with `obj_key`.
    pub fn obj_begin(&mut self) -> PResult<bool> {
        self.expect(b'{')?;
        self.skip_ws();
        if self.buf.get(self.pos) == Some(&b'}') {
            self.pos += 1;
            return Ok(false);
        }
        Ok(true)
    }

    /// Object key: the raw bytes between the quotes. Keys never contain escapes, so a backslash is an error.
    pub fn parse_key(&mut self) -> PResult<&'a [u8]> {
        self.parse_plain_string()
    }

    /// Reads `"key" :` and returns the raw key bytes.
    pub fn obj_key(&mut self) -> PResult<&'a [u8]> {
        let key = self.parse_key()?;
        self.expect(b':')?;
        Ok(key)
    }

    /// After a member value: true if a `,` introduces another member, false
    /// if the object's `}` was consumed.
    pub fn obj_more(&mut self) -> PResult<bool> {
        self.skip_ws();
        match self.buf.get(self.pos) {
            Some(b',') => {
                self.pos += 1;
                Ok(true)
            }
            Some(b'}') => {
                self.pos += 1;
                Ok(false)
            }
            _ => self.err("expected ',' or '}'"),
        }
    }

    /// Begins an array (`[`). Returns false for `[]`, otherwise true.
    pub fn arr_begin(&mut self) -> PResult<bool> {
        self.expect(b'[')?;
        self.skip_ws();
        if self.buf.get(self.pos) == Some(&b']') {
            self.pos += 1;
            return Ok(false);
        }
        Ok(true)
    }

    /// After an element: true if a `,` introduces another element, false if `]` was consumed.
    pub fn arr_more(&mut self) -> PResult<bool> {
        self.skip_ws();
        match self.buf.get(self.pos) {
            Some(b',') => {
                self.pos += 1;
                Ok(true)
            }
            Some(b']') => {
                self.pos += 1;
                Ok(false)
            }
            _ => self.err("expected ',' or ']'"),
        }
    }

    /// Skips any JSON value. Nesting deeper than `MAX_DEPTH` is an error.
    pub fn skip_value(&mut self) -> PResult<()> {
        self.skip_value_at(0)
    }

    fn skip_value_at(&mut self, depth: u32) -> PResult<()> {
        if depth > MAX_DEPTH {
            return self.err("nesting too deep");
        }
        self.skip_ws();
        match self.buf.get(self.pos).copied() {
            Some(b'{') => {
                if self.obj_begin()? {
                    loop {
                        self.skip_string()?;
                        self.expect(b':')?;
                        self.skip_value_at(depth + 1)?;
                        if !self.obj_more()? {
                            break;
                        }
                    }
                }
                Ok(())
            }
            Some(b'[') => {
                if self.arr_begin()? {
                    loop {
                        self.skip_value_at(depth + 1)?;
                        if !self.arr_more()? {
                            break;
                        }
                    }
                }
                Ok(())
            }
            Some(b'"') => self.skip_string(),
            Some(b't') => self.skip_literal(b"true"),
            Some(b'f') => self.skip_literal(b"false"),
            Some(b'n') => self.skip_literal(b"null"),
            Some(b'-') | Some(b'0'..=b'9') => self.skip_number(),
            _ => self.err("expected value"),
        }
    }

    fn skip_string(&mut self) -> PResult<()> {
        self.skip_ws();
        if self.buf.get(self.pos) != Some(&b'"') {
            return self.err("expected string");
        }
        let mut i = self.pos + 1;
        loop {
            match self.buf.get(i) {
                None => {
                    self.pos = i;
                    return self.err("unterminated string");
                }
                Some(b'"') => {
                    self.pos = i + 1;
                    return Ok(());
                }
                Some(b'\\') => i += 2,
                Some(&b) if b < 0x20 => {
                    self.pos = i;
                    return self.err("control character in string");
                }
                Some(_) => i += 1,
            }
        }
    }

    fn skip_literal(&mut self, lit: &[u8]) -> PResult<()> {
        if self.rest().starts_with(lit) {
            self.pos += lit.len();
            Ok(())
        } else {
            self.err("invalid literal")
        }
    }

    fn skip_number(&mut self) -> PResult<()> {
        let start = self.pos;
        while let Some(&b) = self.buf.get(self.pos) {
            if b.is_ascii_digit() || matches!(b, b'-' | b'+' | b'.' | b'e' | b'E') {
                self.pos += 1;
            } else {
                break;
            }
        }
        if !self.buf[start..self.pos].iter().any(u8::is_ascii_digit) {
            return self.err("invalid number");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn string_of(src: &str) -> Result<Vec<u8>, ParseError> {
        let mut c = Cursor::new(src.as_bytes());
        let mut out = Vec::new();
        c.parse_string_into(&mut out)?;
        assert!(c.at_end());
        Ok(out)
    }

    fn decoded(src: &str) -> String {
        String::from_utf8(string_of(src).expect("should decode")).unwrap()
    }

    #[test]
    fn string_simple_escapes() {
        assert_eq!(decoded(r#""a\"b\\c\/d\b\f\n\r\t""#), "a\"b\\c/d\u{8}\u{c}\n\r\t");
        assert_eq!(decoded(r#""""#), "");
        assert_eq!(decoded(r#""plain é 😀""#), "plain é 😀");
    }

    #[test]
    fn string_unicode_escapes() {
        assert_eq!(decoded(r#""αβ""#), "αβ");
        assert_eq!(decoded(r#""\u0000""#), "\u{0}");
        // Surrogate pair decodes to one scalar value.
        assert_eq!(decoded(r#""😀""#), "😀");
        assert_eq!(decoded(r#""x𝒜y""#), "x𝒜y");
    }

    #[test]
    fn string_lone_surrogates_become_replacement() {
        let r = '\u{FFFD}';
        assert_eq!(decoded(r#""\ud83d""#), r.to_string());
        assert_eq!(decoded(r#""\ude00""#), r.to_string());
        assert_eq!(decoded(r#""\ud83dx""#), format!("{r}x"));
        // High surrogate followed by a non-low-surrogate escape: the second escape is kept.
        assert_eq!(decoded(r#""\ud83dA""#), format!("{r}A"));
        // Two highs in a row: the first is replaced, the second pairs with nothing.
        assert_eq!(decoded(r#""\ud83d\ud83d""#), format!("{r}{r}"));
    }

    #[test]
    fn string_errors() {
        assert!(string_of(r#""\x""#).is_err());
        assert!(string_of(r#""\u12""#).is_err());
        assert!(string_of(r#""\u12G4""#).is_err());
        assert!(string_of(r#""abc"#).is_err());
        assert!(string_of("\"a\u{1}b\"").is_err());
        // Invalid UTF-8 inside the string.
        let bytes = b"\"a\xffb\"";
        let mut c = Cursor::new(bytes);
        let mut out = Vec::new();
        assert!(c.parse_string_into(&mut out).is_err());
    }

    #[test]
    fn plain_string_rejects_escapes() {
        let mut c = Cursor::new(br#""safe""#);
        assert_eq!(c.parse_plain_string().unwrap(), b"safe");
        let mut c = Cursor::new(br#""sa\"fe""#);
        assert!(c.parse_plain_string().is_err());
    }

    #[test]
    fn skip_value_nested() {
        let src = r#"{"a":[1,-2.5e+3,{"b":null,"c":[true,false,"x\"}]"]}],"d":"\\"}, 7"#;
        let mut c = Cursor::new(src.as_bytes());
        c.skip_value().unwrap();
        c.expect(b',').unwrap();
        assert_eq!(c.parse_u64().unwrap(), 7);
        assert!(c.at_end());
    }

    #[test]
    fn skip_value_scalars_and_errors() {
        for src in ["0", "-12", "3.25", "1e10", "true", "false", "null", "\"s\"", "[]", "{}"] {
            let mut c = Cursor::new(src.as_bytes());
            c.skip_value().unwrap();
            assert!(c.at_end(), "{src}");
        }
        for src in ["tru", "nul", "[1,]", "{\"a\" 1}", "-", "@", "{\"a\":1"] {
            let mut c = Cursor::new(src.as_bytes());
            assert!(c.skip_value().is_err(), "{src}");
        }
    }

    #[test]
    fn skip_value_depth_limit() {
        let ok = format!("{}{}", "[".repeat(100), "]".repeat(100));
        Cursor::new(ok.as_bytes()).skip_value().unwrap();
        let deep = format!("{}{}", "[".repeat(1000), "]".repeat(1000));
        assert!(Cursor::new(deep.as_bytes()).skip_value().is_err());
    }

    #[test]
    fn u64_bounds() {
        let mut c = Cursor::new(b"18446744073709551615");
        assert_eq!(c.parse_u64().unwrap(), u64::MAX);
        let mut c = Cursor::new(b"18446744073709551616");
        assert!(c.parse_u64().is_err());
        let mut c = Cursor::new(b"99999999999999999999999");
        assert!(c.parse_u64().is_err());
        let mut c = Cursor::new(b"-1");
        assert!(c.parse_u64().is_err());
        let mut c = Cursor::new(b"  0 ");
        assert_eq!(c.parse_u64().unwrap(), 0);
    }

    #[test]
    fn object_and_array_iteration() -> PResult<()> {
        let src = br#"{ "x" : [1, 2], "y": {}, "z": "q" }"#;
        let mut c = Cursor::new(src);
        let mut keys = Vec::new();
        each_key!(c, k => {
            keys.push(k.to_vec());
            match k {
                b"x" => {
                    let mut v = Vec::new();
                    each_elem!(c, { v.push(c.parse_u64()?); });
                    assert_eq!(v, vec![1, 2]);
                }
                _ => c.skip_value()?,
            }
        });
        assert!(c.at_end());
        assert_eq!(keys, vec![b"x".to_vec(), b"y".to_vec(), b"z".to_vec()]);
        Ok(())
    }

    #[test]
    fn bool_and_expect() {
        let mut c = Cursor::new(b" true false x");
        assert!(c.parse_bool().unwrap());
        assert!(!c.parse_bool().unwrap());
        assert!(c.parse_bool().is_err());
        let mut c = Cursor::new(b"  ]");
        assert!(c.expect(b'[').is_err());
    }
}
