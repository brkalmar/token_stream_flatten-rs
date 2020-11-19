//! Flattening iterator adaptor for token streams.
//!
//! Allows processing rust source as a sequence of primitve tokens.
//!
//! # Usage
//!
//! The adaptor [`FlattenRec`] can be obtained by the [`flatten_rec`] method, provided by the trait
//! [`IntoFlattenRec`], implemented for [`proc-macro2`'s `IntoIter`].  This is convenient for method
//! chaining.
//!
//! Alternatively, [`FlattenRec`'s `From<IntoIter>`] implementation can be used directly.
//!
//! ```
//! # use token_stream_flatten::{DelimiterKind, DelimiterPosition, IntoFlattenRec, Token};
//! #
//! let stream = r#"if n > 1 { foo[n - 2] } else { 11 }"#
//!     .parse::<proc_macro2::TokenStream>()
//!     .unwrap();
//! let flat = stream.into_iter().flatten_rec().collect::<Vec<_>>();
//!
//! assert_eq!(
//!     flat.iter().map(|token| token.to_string()).collect::<Vec<_>>(),
//!     vec!["if", "n", ">", "1", "{", "foo", "[", "n", "-", "2", "]", "}", "else", "{", "11", "}"],
//! );
//!
//! assert_eq!(flat[2].span().start(), proc_macro2::LineColumn { line: 1, column: 5 });
//! assert_eq!(flat[2].span().end(), proc_macro2::LineColumn { line: 1, column: 6 });
//! if let Token::Punct(punct) = &flat[2] {
//!     assert_eq!(punct.as_char(), '>');
//! } else {
//!     panic!("expected punct");
//! }
//!
//! assert_eq!(flat[10].span().start(), proc_macro2::LineColumn { line: 1, column: 20 });
//! assert_eq!(flat[10].span().end(), proc_macro2::LineColumn { line: 1, column: 21 });
//! if let Token::Delimiter(delimiter) = &flat[10] {
//!     assert_eq!(delimiter.kind(), DelimiterKind::Bracket);
//!     assert_eq!(delimiter.position(), DelimiterPosition::Close);
//! } else {
//!     panic!("expected delimiter");
//! }
//! ```
//!
//! # Features
//!
//! - `proc-macro`: Enables feature `proc-macro` of [`proc-macro2`] (enabled by default).
//! - `span-locations`: Enables feature `span-locations` of [`proc-macro2`] (enabled by default).
//!
//! [`FlattenRec`]: struct.FlattenRec.html
//! [`FlattenRec`'s `From<IntoIter>`]: struct.FlattenRec.html#impl-From%3CIntoIter%3E
//! [`IntoFlattenRec`]: trait.IntoFlattenRec.html
//! [`flatten_rec`]: trait.IntoFlattenRec.html#tymethod.flatten_rec
//! [`proc-macro2`]: https://docs.rs/proc-macro2/latest/proc_macro2/index.html
//! [`proc-macro2`'s `IntoIter`]:
//! https://docs.rs/proc-macro2/latest/proc_macro2/token_stream/struct.IntoIter.html

use std::{convert, fmt, iter};

/// Iterator adaptor that recursively flattens the token trees of an [`IntoIter`].
///
/// Yields all atomic tokens and delimiters in the order they occur in the source.
///
/// Unpacks each [`Group`] by first yielding the opening delimiter, recursively iterating over the
/// group's inner token stream, then yielding the closing delimiter.  (If the group has a [`None`]
/// delimiter, then no opening or closing delimiter is yielded.)  All other tokens of the underlying
/// [`IntoIter`] are simply converted to [`Token`]s.
///
/// [`Group`]: https://docs.rs/proc-macro2/latest/proc_macro2/struct.Group.html
/// [`IntoIter`]: https://docs.rs/proc-macro2/latest/proc_macro2/token_stream/struct.IntoIter.html
/// [`None`]: https://docs.rs/proc-macro2/latest/proc_macro2/enum.Delimiter.html#variant.None
/// [`Token`]: enum.Token.html
#[derive(Clone, Debug)]
pub struct FlattenRec {
    stack: Vec<GroupIter>,
}

/// A group's stream iterator and its open and close delimiter, which may be absent.
#[derive(Clone, Debug)]
struct GroupIter {
    open: Option<DelimiterInner>,
    iter: proc_macro2::token_stream::IntoIter,
    close: Option<DelimiterInner>,
}

/// Single atomic token.
///
/// Either wraps one of [`proc-macro2`]'s token types, or a delimiter.
///
/// [`proc-macro2`]: https://docs.rs/proc-macro2/latest/proc_macro2/index.html
#[derive(Clone, Debug)]
pub enum Token {
    /// Delimiter.
    Delimiter(Delimiter),

    /// Identifier.
    Ident(proc_macro2::Ident),

    /// Literal (character, string, number, etc.).
    Literal(proc_macro2::Literal),

    /// Single punctuation character.
    Punct(proc_macro2::Punct),
}

/// Single delimiter token.
#[derive(Clone)]
pub struct Delimiter {
    inner: DelimiterInner,
    position: DelimiterPosition,
}

/// Delimiter without position information.
#[derive(Clone, Debug)]
struct DelimiterInner {
    kind: DelimiterKind,
    span: proc_macro2::Span,
}

/// The kind of a delimiter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DelimiterKind {
    /// `{` and `}`.
    Brace,

    /// `[` and `]`.
    Bracket,

    /// `(` and `)`.
    Parenthesis,
}

/// Whether a delimiter is opening or closing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DelimiterPosition {
    /// Opening delimiter (`{`, `[`, ...).
    Open,

    /// Closing delimiter (`}`, `]`, ...).
    Close,
}

/// Allows conversion into [`FlattenRec`].
///
/// [`FlattenRec`]: struct.FlattenRec.html
pub trait IntoFlattenRec {
    /// Convert into a flattening iterator adaptor.
    fn flatten_rec(self) -> FlattenRec;
}

impl From<proc_macro2::token_stream::IntoIter> for FlattenRec {
    fn from(iter: proc_macro2::token_stream::IntoIter) -> Self {
        Self {
            stack: vec![iter.into()],
        }
    }
}

impl Iterator for FlattenRec {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        use convert::TryInto;
        use DelimiterPosition::*;
        while let Some(group_iter) = self.stack.last_mut() {
            match group_iter.iter.next() {
                Some(tree) => match tree.try_into() {
                    Ok(token) => return Some(token),
                    Err(group) => {
                        let group_iter = GroupIter::from(group);
                        let open = group_iter.open.clone();
                        self.stack.push(group_iter);
                        if let Some(open) = open {
                            return Some(Token::Delimiter(Delimiter::from_inner(open, Open)));
                        }
                    }
                },
                None => {
                    let close = group_iter.close.clone();
                    self.stack.pop();
                    if let Some(close) = close {
                        return Some(Token::Delimiter(Delimiter::from_inner(close, Close)));
                    }
                }
            }
        }
        None
    }
}

impl iter::FusedIterator for FlattenRec {}

/// Create group iterator directly from stream iterator, with no enclosing delimiters.
impl From<proc_macro2::token_stream::IntoIter> for GroupIter {
    fn from(iter: proc_macro2::token_stream::IntoIter) -> Self {
        Self {
            open: None,
            iter: iter,
            close: None,
        }
    }
}

/// Create group iterator with the given group's delimiters and inner stream iterator.
impl From<proc_macro2::Group> for GroupIter {
    fn from(group: proc_macro2::Group) -> Self {
        use convert::TryInto;

        let delimiter_kind = group.delimiter().try_into().ok();
        let open = delimiter_kind.map(|kind| DelimiterInner {
            kind: kind,
            span: group.span_open(),
        });
        let close = delimiter_kind.map(|kind| DelimiterInner {
            kind: kind,
            span: group.span_close(),
        });
        let iter = group.stream().into_iter();
        Self { open, iter, close }
    }
}

impl Token {
    /// The span of the token.
    pub fn span(&self) -> proc_macro2::Span {
        use Token::*;
        match self {
            Delimiter(delimiter) => delimiter.span(),
            Ident(ident) => ident.span(),
            Literal(literal) => literal.span(),
            Punct(punct) => punct.span(),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;
        match self {
            Delimiter(delimiter) => fmt::Display::fmt(delimiter, f),
            Ident(ident) => fmt::Display::fmt(ident, f),
            Literal(literal) => fmt::Display::fmt(literal, f),
            Punct(punct) => fmt::Display::fmt(punct, f),
        }
    }
}

impl From<Delimiter> for Token {
    fn from(delimiter: Delimiter) -> Self {
        Self::Delimiter(delimiter)
    }
}

impl From<proc_macro2::Ident> for Token {
    fn from(ident: proc_macro2::Ident) -> Self {
        Self::Ident(ident)
    }
}

impl From<proc_macro2::Literal> for Token {
    fn from(literal: proc_macro2::Literal) -> Self {
        Self::Literal(literal)
    }
}

impl From<proc_macro2::Punct> for Token {
    fn from(punct: proc_macro2::Punct) -> Self {
        Self::Punct(punct)
    }
}

/// Any token tree except group is directly convertible to a corresponing [`Token`].
///
/// [`Token`]: enum.Token.html
impl convert::TryFrom<proc_macro2::TokenTree> for Token {
    type Error = proc_macro2::Group;

    fn try_from(tree: proc_macro2::TokenTree) -> Result<Self, Self::Error> {
        use proc_macro2::TokenTree::*;
        match tree {
            Group(group) => Err(group),
            Ident(ident) => Ok(ident.into()),
            Literal(literal) => Ok(literal.into()),
            Punct(punct) => Ok(punct.into()),
        }
    }
}

impl Delimiter {
    /// Create new delimiter with the specified attributes and span.
    pub fn new(kind: DelimiterKind, position: DelimiterPosition, span: proc_macro2::Span) -> Self {
        let inner = DelimiterInner { kind, span };
        Self::from_inner(inner, position)
    }

    fn from_inner(inner: DelimiterInner, position: DelimiterPosition) -> Self {
        Self { inner, position }
    }

    /// The delimiter's kind.
    pub fn kind(&self) -> DelimiterKind {
        self.inner.kind
    }

    /// The delimiter's position.
    pub fn position(&self) -> DelimiterPosition {
        self.position
    }

    /// The delimiter's span.
    pub fn span(&self) -> proc_macro2::Span {
        self.inner.span
    }
}

impl fmt::Debug for Delimiter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Delimiter")
            .field("kind", &self.kind())
            .field("position", &self.position())
            .field("span", &self.span())
            .finish()
    }
}

impl fmt::Display for Delimiter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DelimiterKind::*;
        use DelimiterPosition::*;
        fmt::Display::fmt(
            match self.kind() {
                Brace => match self.position() {
                    Open => "{",
                    Close => "}",
                },
                Bracket => match self.position() {
                    Open => "[",
                    Close => "]",
                },
                Parenthesis => match self.position() {
                    Open => "(",
                    Close => ")",
                },
            },
            f,
        )
    }
}

/// Any delimiter except [`None`] is directly convertible to a corresponing [`DelimiterKind`].
///
/// [`DelimiterKind`]: enum.DelimiterKind.html
/// [`None`]: https://docs.rs/proc-macro2/latest/proc_macro2/enum.Delimiter.html#variant.None
impl convert::TryFrom<proc_macro2::Delimiter> for DelimiterKind {
    type Error = ();

    fn try_from(delimiter: proc_macro2::Delimiter) -> Result<Self, Self::Error> {
        use DelimiterKind::*;
        match delimiter {
            proc_macro2::Delimiter::Brace => Ok(Brace),
            proc_macro2::Delimiter::Bracket => Ok(Bracket),
            proc_macro2::Delimiter::None => Err(()),
            proc_macro2::Delimiter::Parenthesis => Ok(Parenthesis),
        }
    }
}

impl IntoFlattenRec for proc_macro2::token_stream::IntoIter {
    fn flatten_rec(self) -> FlattenRec {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::{LineColumn, Literal, TokenStream};

    macro_rules! assert_eq_token_span {
        (
            $token:expr,
            ($start_line:expr, $start_col:expr)..($end_line:expr, $end_col:expr) $(,)?
        ) => {
            assert_eq!(
                $token.span().start(),
                LineColumn {
                    line: $start_line,
                    column: $start_col
                }
            );
            assert_eq!(
                $token.span().end(),
                LineColumn {
                    line: $end_line,
                    column: $end_col
                }
            );
        };
    }

    macro_rules! assert_eq_token {
        (
            $token:expr,
            (
                ($start_line:expr, $start_col:expr)..($end_line:expr, $end_col:expr),
                Delimiter($kind:ident, $pos:ident) $(,)?
            ) $(,)?
        ) => {
            assert_eq_token_span!($token, ($start_line, $start_col)..($end_line, $end_col));
            match $token {
                Token::Delimiter(delimiter) => {
                    assert_eq!(delimiter.kind(), DelimiterKind::$kind);
                    assert_eq!(delimiter.position(), DelimiterPosition::$pos);
                }
                _ => panic!("token is not Delimiter: {:?}", $token),
            }
        };
        (
            $token:expr,
            (
                ($start_line:expr, $start_col:expr)..($end_line:expr, $end_col:expr),
                Ident($s:expr) $(,)?
            ) $(,)?
        ) => {
            assert_eq_token_span!($token, ($start_line, $start_col)..($end_line, $end_col));
            match $token {
                Token::Ident(ident) => assert_eq!(ident.to_string(), $s),
                _ => panic!("token is not Ident: {:?}", $token),
            }
        };
        (
            $token:expr,
            (
                ($start_line:expr, $start_col:expr)..($end_line:expr, $end_col:expr),
                Literal::$lit_fn:ident($($lit_args:expr),*) $(,)?
            ) $(,)?
        ) => {
            assert_eq_token_span!($token, ($start_line, $start_col)..($end_line, $end_col));
            match $token {
                Token::Literal(literal) => assert_eq!(literal.to_string(),
                                                      Literal::$lit_fn($($lit_args),*).to_string()),
                _ => panic!("token is not Literal: {:?}", $token),
            }
        };
        (
            $token:expr,
            (
                ($start_line:expr, $start_col:expr)..($end_line:expr, $end_col:expr),
                Punct($c:expr) $(,)?
            ) $(,)?
        ) => {
            assert_eq_token_span!($token, ($start_line, $start_col)..($end_line, $end_col));
            match $token {
                Token::Punct(punct) => assert_eq!(punct.as_char(), $c),
                _ => panic!("token is not Punct: {:?}", $token),
            }
        };
    }

    macro_rules! assert_eq_tokens {
        (
            $tokens:expr,
            $($expected:tt),* $(,)?
        ) => {{
            let mut tokens = $tokens.into_iter();
            $({
                let token = tokens.next().unwrap();
                assert_eq_token!(token, $expected);
            })*
            assert!(tokens.next().is_none());
        }}
    }

    #[test]
    fn delimiters_nested() {
        let stream = r#"
{
    {
        true;
        f()
    }
    a[0] = b[Self { (3 * i) + 1 }];
}
print(a[5])
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 1), Delimiter(Brace, Open)),
            ((3, 4)..(3, 5), Delimiter(Brace, Open)),
            ((4, 8)..(4, 12), Ident("true")),
            ((4, 12)..(4, 13), Punct(';')),
            ((5, 8)..(5, 9), Ident("f")),
            ((5, 9)..(5, 10), Delimiter(Parenthesis, Open)),
            ((5, 10)..(5, 11), Delimiter(Parenthesis, Close)),
            ((6, 4)..(6, 5), Delimiter(Brace, Close)),
            ((7, 4)..(7, 5), Ident("a")),
            ((7, 5)..(7, 6), Delimiter(Bracket, Open)),
            ((7, 6)..(7, 7), Literal::usize_unsuffixed(0)),
            ((7, 7)..(7, 8), Delimiter(Bracket, Close)),
            ((7, 9)..(7, 10), Punct('=')),
            ((7, 11)..(7, 12), Ident("b")),
            ((7, 12)..(7, 13), Delimiter(Bracket, Open)),
            ((7, 13)..(7, 17), Ident("Self")),
            ((7, 18)..(7, 19), Delimiter(Brace, Open)),
            ((7, 20)..(7, 21), Delimiter(Parenthesis, Open)),
            ((7, 21)..(7, 22), Literal::usize_unsuffixed(3)),
            ((7, 23)..(7, 24), Punct('*')),
            ((7, 25)..(7, 26), Ident("i")),
            ((7, 26)..(7, 27), Delimiter(Parenthesis, Close)),
            ((7, 28)..(7, 29), Punct('+')),
            ((7, 30)..(7, 31), Literal::usize_unsuffixed(1)),
            ((7, 32)..(7, 33), Delimiter(Brace, Close)),
            ((7, 33)..(7, 34), Delimiter(Bracket, Close)),
            ((7, 34)..(7, 35), Punct(';')),
            ((8, 0)..(8, 1), Delimiter(Brace, Close)),
            ((9, 0)..(9, 5), Ident("print")),
            ((9, 5)..(9, 6), Delimiter(Parenthesis, Open)),
            ((9, 6)..(9, 7), Ident("a")),
            ((9, 7)..(9, 8), Delimiter(Bracket, Open)),
            ((9, 8)..(9, 9), Literal::usize_unsuffixed(5)),
            ((9, 9)..(9, 10), Delimiter(Bracket, Close)),
            ((9, 10)..(9, 11), Delimiter(Parenthesis, Close)),
        );
    }

    #[test]
    fn delimiter() {
        let stream = r#"
x[0] q(43) if d { St }
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 1), Ident("x")),
            ((2, 1)..(2, 2), Delimiter(Bracket, Open)),
            ((2, 2)..(2, 3), Literal::i32_unsuffixed(0)),
            ((2, 3)..(2, 4), Delimiter(Bracket, Close)),
            ((2, 5)..(2, 6), Ident("q")),
            ((2, 6)..(2, 7), Delimiter(Parenthesis, Open)),
            ((2, 7)..(2, 9), Literal::i32_unsuffixed(43)),
            ((2, 9)..(2, 10), Delimiter(Parenthesis, Close)),
            ((2, 11)..(2, 13), Ident("if")),
            ((2, 14)..(2, 15), Ident("d")),
            ((2, 16)..(2, 17), Delimiter(Brace, Open)),
            ((2, 18)..(2, 20), Ident("St")),
            ((2, 21)..(2, 22), Delimiter(Brace, Close)),
        );
    }

    #[test]
    fn ident() {
        let stream = r#"
z foo_bar FooBar _ _out-inc18 υ 敗れる héllő_wørld_020 'static true
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 1), Ident("z")),
            ((2, 2)..(2, 9), Ident("foo_bar")),
            ((2, 10)..(2, 16), Ident("FooBar")),
            ((2, 17)..(2, 18), Ident("_")),
            ((2, 19)..(2, 23), Ident("_out")),
            ((2, 23)..(2, 24), Punct('-')),
            ((2, 24)..(2, 29), Ident("inc18")),
            ((2, 30)..(2, 31), Ident("υ")),
            ((2, 32)..(2, 35), Ident("敗れる")),
            ((2, 36)..(2, 51), Ident("héllő_wørld_020")),
            ((2, 52)..(2, 53), Punct('\'')),
            ((2, 53)..(2, 59), Ident("static")),
            ((2, 60)..(2, 64), Ident("true")),
        );
    }

    #[test]
    fn literal() {
        let stream = r#"
33554432u32 33554432isize 33554432
1.442695f32 1.442695f64 1.442695
b"L4l" '\t' "блакить ┇ m³"
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 11), Literal::u32_suffixed(33554432)),
            ((2, 12)..(2, 25), Literal::isize_suffixed(33554432)),
            ((2, 26)..(2, 34), Literal::i32_unsuffixed(33554432)),
            ((3, 0)..(3, 11), Literal::f32_suffixed(1.442695)),
            ((3, 12)..(3, 23), Literal::f64_suffixed(1.442695)),
            ((3, 24)..(3, 32), Literal::f64_unsuffixed(1.442695)),
            ((4, 0)..(4, 6), Literal::byte_string(b"L4l")),
            ((4, 7)..(4, 11), Literal::character('\t')),
            ((4, 12)..(4, 26), Literal::string("блакить ┇ m³")),
        );
    }

    #[test]
    fn punct() {
        let stream = r#"
j..=k; fun::<u64>() * &3
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 1), Ident("j")),
            ((2, 1)..(2, 2), Punct('.')),
            ((2, 2)..(2, 3), Punct('.')),
            ((2, 3)..(2, 4), Punct('=')),
            ((2, 4)..(2, 5), Ident("k")),
            ((2, 5)..(2, 6), Punct(';')),
            ((2, 7)..(2, 10), Ident("fun")),
            ((2, 10)..(2, 11), Punct(':')),
            ((2, 11)..(2, 12), Punct(':')),
            ((2, 12)..(2, 13), Punct('<')),
            ((2, 13)..(2, 16), Ident("u64")),
            ((2, 16)..(2, 17), Punct('>')),
            ((2, 17)..(2, 18), Delimiter(Parenthesis, Open)),
            ((2, 18)..(2, 19), Delimiter(Parenthesis, Close)),
            ((2, 20)..(2, 21), Punct('*')),
            ((2, 22)..(2, 23), Punct('&')),
            ((2, 23)..(2, 24), Literal::i32_unsuffixed(3)),
        );
    }

    #[test]
    fn comment_line() {
        let stream = r#"
a = 5;
// Alpha, beta, gamma; delta...
b != 'x'
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 1), Ident("a")),
            ((2, 2)..(2, 3), Punct('=')),
            ((2, 4)..(2, 5), Literal::i32_unsuffixed(5)),
            ((2, 5)..(2, 6), Punct(';')),
            ((4, 0)..(4, 1), Ident("b")),
            ((4, 2)..(4, 3), Punct('!')),
            ((4, 3)..(4, 4), Punct('=')),
            ((4, 5)..(4, 8), Literal::character('x')),
        );
    }

    #[test]
    fn doc_line_inner() {
        let stream = r#"
mod m {
    //! a
    //! bc
    struct S;
}
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 3), Ident("mod")),
            ((2, 4)..(2, 5), Ident("m")),
            ((2, 6)..(2, 7), Delimiter(Brace, Open)),
            ((3, 4)..(3, 9), Punct('#')),
            ((3, 4)..(3, 9), Punct('!')),
            ((3, 4)..(3, 5), Delimiter(Bracket, Open)),
            ((3, 4)..(3, 9), Ident("doc")),
            ((3, 4)..(3, 9), Punct('=')),
            ((3, 4)..(3, 9), Literal::string(" a")),
            ((3, 8)..(3, 9), Delimiter(Bracket, Close)),
            ((4, 4)..(4, 10), Punct('#')),
            ((4, 4)..(4, 10), Punct('!')),
            ((4, 4)..(4, 5), Delimiter(Bracket, Open)),
            ((4, 4)..(4, 10), Ident("doc")),
            ((4, 4)..(4, 10), Punct('=')),
            ((4, 4)..(4, 10), Literal::string(" bc")),
            ((4, 9)..(4, 10), Delimiter(Bracket, Close)),
            ((5, 4)..(5, 10), Ident("struct")),
            ((5, 11)..(5, 12), Ident("S")),
            ((5, 12)..(5, 13), Punct(';')),
            ((6, 0)..(6, 1), Delimiter(Brace, Close)),
        );
    }
    #[test]

    fn doc_line_outer() {
        let stream = r#"
/// Foo bar
/// baz.
enum X {}
"#
        .parse::<TokenStream>()
        .unwrap();

        assert_eq_tokens!(
            stream.into_iter().flatten_rec(),
            ((2, 0)..(2, 11), Punct('#')),
            ((2, 0)..(2, 1), Delimiter(Bracket, Open)),
            ((2, 0)..(2, 11), Ident("doc")),
            ((2, 0)..(2, 11), Punct('=')),
            ((2, 0)..(2, 11), Literal::string(" Foo bar")),
            ((2, 10)..(2, 11), Delimiter(Bracket, Close)),
            ((3, 0)..(3, 8), Punct('#')),
            ((3, 0)..(3, 1), Delimiter(Bracket, Open)),
            ((3, 0)..(3, 8), Ident("doc")),
            ((3, 0)..(3, 8), Punct('=')),
            ((3, 0)..(3, 8), Literal::string(" baz.")),
            ((3, 7)..(3, 8), Delimiter(Bracket, Close)),
            ((4, 0)..(4, 4), Ident("enum")),
            ((4, 5)..(4, 6), Ident("X")),
            ((4, 7)..(4, 8), Delimiter(Brace, Open)),
            ((4, 8)..(4, 9), Delimiter(Brace, Close)),
        );
    }
}
