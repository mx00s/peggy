use std::{
    collections::HashMap,
    fmt::Debug,
    ops::{Deref, Index},
};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {}

// alphabet's letters must be unique (and, in case of ranges, non-overlapping)
pub trait Alphabet: Clone + Debug + PartialEq + Eq {}

// non_terminals must be unique
pub trait NonTerminals: Clone + Debug + PartialEq + Eq {}

// labels must be unique
pub trait LabelSymbols: Clone + Debug + PartialEq + Eq {}

pub trait CoreTypes: Clone + Debug {
    type NonTerminal: NonTerminals;
    type Alphabet: Alphabet;
    type Label: LabelSymbols;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<T>
where
    T: CoreTypes,
{
    // ε
    Empty,
    // a
    Terminal(T::Alphabet),
    // A
    NonTerminal(T::NonTerminal),
    // e1 e2
    Sequence(Box<Self>, Box<Self>),
    // e1 / e2
    OrderedChoice(Box<Self>, Box<Self>),
    // e*
    ZeroOrMore(Box<Self>),
    // !e
    Not(Box<Self>),
    // {e #L}
    Capture(Box<Self>, T::Label),
    // e1 ^* {e2 #L}
    FoldCapture(Box<Self>, (Box<Self>, T::Label)),
}

impl<T> Expression<T>
where
    T: CoreTypes,
{
    pub fn from_non_terminal(non_terminal: T::NonTerminal) -> Self {
        Self::NonTerminal(non_terminal)
    }

    pub fn from_terminal(terminal: T::Alphabet) -> Self {
        Self::Terminal(terminal)
    }

    // e+ ==> e e*
    pub fn one_or_more(&self) -> Self {
        Self::Sequence(
            Box::new((*self).clone()),
            Box::new(Self::ZeroOrMore(Box::new((*self).clone()))),
        )
    }

    // [abc] ==> 'a' / 'b' / 'c'
    pub fn any_of(exprs: &[Self]) -> Option<Self> {
        exprs.iter().rfold(None, |acc, head| {
            Some(acc.map_or_else(
                || head.clone(),
                |tail| Self::OrderedChoice(Box::new(head.clone()), Box::new(tail)),
            ))
        })
    }

    // e? ==> e / ε
    pub fn optional(&self) -> Self {
        Self::OrderedChoice(Box::new(self.clone()), Box::new(Self::Empty))
    }

    // &e ==> !(!e)
    pub fn and(&self) -> Self {
        Self::Not(Box::new(Self::Not(Box::new(self.clone()))))
    }
}

#[derive(Clone, Debug)]
pub enum Tree<T: CoreTypes> {
    Label(T::Label, Box<Self>),
    Concatenation(Box<Self>, Box<Self>),
    // TODO: refactor to avoid redundant clones of parts of the input
    String(Vec<T::Alphabet>),
}

impl<T: CoreTypes> Tree<T> {
    fn canonicalize(&self) -> Self {
        match self {
            Tree::Label(l, v) => Tree::Label(l.clone(), Box::new(v.canonicalize())),
            Tree::Concatenation(v1, v2) => match (v1.deref(), v2.deref()) {
                (Tree::Label(l, v), Tree::String(_)) | (Tree::String(_), Tree::Label(l, v)) => {
                    Tree::Label(l.to_owned(), Box::new(v.canonicalize()))
                }
                (v @ Tree::Concatenation(_, _), Tree::String(s2)) => match v.canonicalize() {
                    Tree::String(s1) => Self::String([s1.to_owned(), s2.to_owned()].concat()),
                    _v => todo!(),
                },
                (Tree::String(s1), v @ Tree::Concatenation(_, _)) => match v.canonicalize() {
                    Tree::String(s2) => Self::String([s1.to_owned(), s2.to_owned()].concat()),
                    _v => todo!(),
                },
                (Tree::String(s1), Tree::String(s2)) => {
                    Self::String([s1.to_owned(), s2.to_owned()].concat())
                }
                (v1, v2) => {
                    Tree::Concatenation(Box::new(v1.canonicalize()), Box::new(v2.canonicalize()))
                }
            },
            Tree::String(s) => Tree::String(s.to_owned()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeVar(usize);

#[derive(Clone, Debug)]
pub enum RegularExpressionType<T: CoreTypes> {
    Empty,
    Concatenation(Box<Self>, Box<Self>),
    Union(Box<Self>, Box<Self>),
    ZeroOrMore(Box<Self>),
    Label(T::Label, Vec<Self>),
    Var(TypeVar),
}

impl<T: CoreTypes> From<Tree<T>> for RegularExpressionType<T> {
    fn from(_: Tree<T>) -> Self {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct TypeMap<T: CoreTypes>(HashMap<TypeVar, RegularExpressionType<T>>);

impl<T: CoreTypes> TypeMap<T> {
    fn derive(expr: &Expression<T>) -> Result<(Self, RegularExpressionType<T>), Error> {
        // See Fig 3 for typing rules for `Tree`s
        //   NOTE: S-VAR rule depends on global set `E`, so the tree type is
        //   derived along the way.

        // See Fig 4 for typing rules for a single global set `E`: maps an
        // `Expression` to a `RegularExpressionType` under a typing environment
        // (gamma) with a global set `E` and a set of used type variables.

        todo!("derive global set E and tree type from expression");
    }
}

// TODO: Consider how to represent the "single global set `E`" which maps
// `TypeVar`s to `RegularExpressionType`s.

// TODO: elaborate
pub struct Derivation<'a, T: CoreTypes> {
    tree: Tree<T>,
    unconsumed_input: &'a [T::Alphabet],
    ret: RegularExpressionType<T>,
    global_set: TypeMap<T>,
}

pub trait Grammar<T>: Index<T::NonTerminal, Output = Expression<T>>
where
    T: CoreTypes,
{
    fn parse<'a>(
        &self,
        expr: &Expression<T>,
        input: &'a [T::Alphabet],
    ) -> Result<Derivation<'a, T>, Error> {
        let (tree, unconsumed_input) = self.derive_tree(expr, input);

        // TODO: clean up
        if tree.is_none() {
            todo!("return error");
        }
        let tree = tree.unwrap().canonicalize();
        dbg!(&tree);
        dbg!(&unconsumed_input);

        let (global_set, ret) = TypeMap::derive(expr)?;

        dbg!(&global_set);
        dbg!(&ret);

        Ok(Derivation {
            tree,
            unconsumed_input,
            ret,
            global_set,
        })
    }

    fn derive_tree<'a>(
        &self,
        expr: &Expression<T>,
        input: &'a [T::Alphabet],
    ) -> (Option<Tree<T>>, &'a [T::Alphabet]) {
        // See Fig 2 for `Tree` derivation (`v`): expression `e` parses an input
        //   `x` and transforms it to an output `o` with an unconsumed string
        //   `y`. (The output is an `Option` to account for potential failure.)

        match expr {
            // E-Empty
            Expression::Empty => (Some(Tree::String(vec![])), input),
            Expression::Terminal(x) => {
                if input.is_empty() {
                    // TODO: Fig 2 doesn't have a rule for this case; verify this is correct
                    (None, input)
                } else {
                    if *x == input[0] {
                        // E-Term1
                        (Some(Tree::String((&input[0..1]).to_vec())), &input[1..])
                    } else {
                        // E-Term2
                        (None, &input[1..])
                    }
                }
            }
            // E-Nt
            Expression::NonTerminal(nt) => self.derive_tree(&self[nt.to_owned()], input),
            Expression::Sequence(e1, e2) => {
                let (v1, x2_z) = self.derive_tree(e1, input);
                if let Some(v1) = v1 {
                    let (v2, z) = self.derive_tree(e2, x2_z);
                    if let Some(v2) = v2 {
                        // E-Seq1
                        (Some(Tree::Concatenation(Box::new(v1), Box::new(v2))), z)
                    } else {
                        // E-Seq3
                        (None, input)
                    }
                } else {
                    // E-Seq2
                    (None, input)
                }
            }
            Expression::OrderedChoice(e1, e2) => {
                let (v1, y) = self.derive_tree(e1, input);
                if let Some(v1) = v1 {
                    // E-Alt1
                    (Some(v1), y)
                } else {
                    let (v2, y) = self.derive_tree(e2, input);
                    if let Some(v2) = v2 {
                        // E-Alt2
                        (Some(v2), y)
                    } else {
                        // E-Alt3
                        (None, input)
                    }
                }
            }
            Expression::ZeroOrMore(e) => {
                match self.derive_tree(e, input) {
                    (Some(v1), x2_y) => {
                        let (v2, y) = self.derive_tree(&Expression::ZeroOrMore(e.to_owned()), x2_y);
                        let v2 = v2.unwrap_or_else(|| {
                            unreachable!(
                                "deriving a tree for a zero-or-more expression always succeeds"
                            )
                        });
                        // E-Rep1
                        (Some(Tree::Concatenation(Box::new(v1), Box::new(v2))), y)
                    }
                    // E-Rep2
                    (None, _) => (Some(Tree::String(vec![])), input),
                }
            }
            Expression::Not(e) => match self.derive_tree(e, input) {
                // E-Not1
                (Some(_), _) => (None, input),
                // E-Not2
                (None, _) => (Some(Tree::String(vec![])), input),
            },
            Expression::Capture(e, l) => {
                let (v, y) = self.derive_tree(e, input);
                if let Some(v) = v {
                    // E-Capture1
                    (Some(Tree::Label(l.clone(), Box::new(v))), y)
                } else {
                    // E-Capture2
                    (None, input)
                }
            }
            Expression::FoldCapture(e1, (e2, l)) => {
                let (v1, input) = self.derive_tree(e1, input);
                if let Some(v1) = v1 {
                    let mut trees = Vec::new();
                    let mut rest = input;
                    while let (Some(vn), input) = self.derive_tree(e2, rest) {
                        rest = input;
                        trees.push(vn);
                    }
                    if let Some((v2, vs)) = trees.split_first() {
                        // E-FoldCap1
                        (
                            Some(vs.iter().fold(
                                Tree::Label(
                                    l.clone(),
                                    Box::new(Tree::Concatenation(
                                        Box::new(v1.clone()),
                                        Box::new(v2.clone()),
                                    )),
                                ),
                                |acc, v| Tree::Concatenation(Box::new(acc), Box::new(v.clone())),
                            )),
                            rest,
                        )
                    } else {
                        // E-FoldCap3
                        (Some(v1), input)
                    }
                } else {
                    // E-FoldCap2
                    (None, input)
                }
            }
        }
    }
}
