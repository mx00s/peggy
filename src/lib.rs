use std::ops::Index;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {}

// alphabet's letters must be unique (and, in case of ranges, non-overlapping)
pub trait Alphabet: Clone {}

// non_terminals must be unique
pub trait NonTerminals: Clone {}

// labels must be unique
pub trait LabelSymbols: Clone {}

pub trait CoreTypes: Clone {
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

// TODO: elaborate
pub struct Derivation;

pub trait Grammar<T>: Index<T::NonTerminal, Output = Expression<T>>
where
    T: CoreTypes,
{
    fn parse(&self, expr: &Expression<T>, input: &[T::Alphabet]) -> Result<Derivation, Error>;
}
