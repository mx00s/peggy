// Eventually most of this will be replaced by macros, but for now it's useful
// to iterate on the internal macro-free interface.

use std::ops::Index;

use anyhow::Result;
use once_cell::sync::Lazy;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NonTerminal {
    Prod,
    Val,
}

impl peggy::NonTerminals for NonTerminal {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Letter {
    L0,
    L1,
    L2,
    L3,
    L4,
    L5,
    L6,
    L7,
    L8,
    L9,
    LMul,
}

impl peggy::Alphabet for Letter {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Label {
    Prod,
    Int,
}

impl peggy::LabelSymbols for Label {}

// Val ^* {× Val #Prod}
static PROD: Lazy<peggy::Expression<Core>> = Lazy::new(|| {
    peggy::Expression::FoldCapture(
        Box::new(peggy::Expression::from_non_terminal(NonTerminal::Val)),
        (
            Box::new(peggy::Expression::Sequence(
                Box::new(peggy::Expression::from_terminal(Letter::LMul.into())),
                Box::new(peggy::Expression::from_non_terminal(NonTerminal::Val)),
            )),
            Label::Prod,
        ),
    )
});

// {[0123456789]+ #Int}
static VAL: Lazy<peggy::Expression<Core>> = Lazy::new(|| {
    peggy::Expression::Capture(
        Box::new(
            peggy::Expression::OrderedChoice(
                Box::new(peggy::Expression::from_terminal(Letter::L0)),
                Box::new(peggy::Expression::OrderedChoice(
                    Box::new(peggy::Expression::from_terminal(Letter::L1)),
                    Box::new(peggy::Expression::OrderedChoice(
                        Box::new(peggy::Expression::from_terminal(Letter::L2)),
                        Box::new(peggy::Expression::OrderedChoice(
                            Box::new(peggy::Expression::from_terminal(Letter::L3)),
                            Box::new(peggy::Expression::OrderedChoice(
                                Box::new(peggy::Expression::from_terminal(Letter::L4)),
                                Box::new(peggy::Expression::OrderedChoice(
                                    Box::new(peggy::Expression::from_terminal(Letter::L5)),
                                    Box::new(peggy::Expression::OrderedChoice(
                                        Box::new(peggy::Expression::from_terminal(Letter::L6)),
                                        Box::new(peggy::Expression::OrderedChoice(
                                            Box::new(peggy::Expression::from_terminal(Letter::L7)),
                                            Box::new(peggy::Expression::OrderedChoice(
                                                Box::new(peggy::Expression::from_terminal(
                                                    Letter::L8,
                                                )),
                                                Box::new(peggy::Expression::from_terminal(
                                                    Letter::L9,
                                                )),
                                            )),
                                        )),
                                    )),
                                )),
                            )),
                        )),
                    )),
                )),
            )
            .one_or_more(),
        ),
        Label::Int,
    )
});

#[derive(Clone, Debug)]
struct Core;

impl peggy::CoreTypes for Core {
    type NonTerminal = NonTerminal;
    type Alphabet = Letter;
    type Label = Label;
}

struct Grammar;

impl Index<NonTerminal> for Grammar {
    type Output = peggy::Expression<Core>;

    fn index(&self, index: NonTerminal) -> &Self::Output {
        match index {
            NonTerminal::Prod => &PROD,
            NonTerminal::Val => &VAL,
        }
    }
}

impl peggy::Grammar<Core> for Grammar {}

fn main() -> Result<()> {
    use peggy::Grammar;

    const INPUT: &str = "123×45×6";

    let grammar = Grammar;

    let start_expr = peggy::Expression::from_non_terminal(NonTerminal::Prod);

    // naive letter lexer
    let input = INPUT
        .chars()
        .map(|l| match l {
            '0' => Letter::L0,
            '1' => Letter::L1,
            '2' => Letter::L2,
            '3' => Letter::L3,
            '4' => Letter::L4,
            '5' => Letter::L5,
            '6' => Letter::L6,
            '7' => Letter::L7,
            '8' => Letter::L8,
            '9' => Letter::L9,
            '×' => Letter::LMul,
            _ => todo!("handle invalid input"),
        })
        .collect::<Vec<_>>();

    let derivation = grammar.parse(&start_expr, &input)?;

    // TODO: ensure `derivation` has the same information found in `derivation.txt`

    // TODO: ensure `derivation` encodes a concrete syntax tree that can
    //   precisely reconstruct `INPUT`.

    Ok(())
}
