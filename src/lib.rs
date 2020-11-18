//! Flattening iterator adaptor for token streams.
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
