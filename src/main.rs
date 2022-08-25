#![allow(unused)]

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::{
    error::Error,
    iterators::{Pair, Pairs},
    Parser,
};

#[derive(Parser)]
#[grammar = "../pest/grammar.pest"]
struct TParser;

#[derive(PartialEq, Debug, Clone)]
enum Expr {
    Call { name: String, args: Vec<Expr> },
    Ident(String),
    Number(f32),
    String(String),
}

#[derive(PartialEq, Debug, Clone)]
enum Statement {
    VarDec {
        name: String,
        expr: Expr,
    },
    FunDec {
        name: String,
        args: Vec<String>,
        body: Vec<Expr>,
    },
}

#[derive(PartialEq, Debug, Clone)]
enum AstNode {
    Expr(Expr),
    Statement(Statement),
}

fn parse(source: &str) -> Result<Vec<AstNode>, Error<Rule>> {
    let mut ast = vec![];

    let pairs: Pairs<Rule> = TParser::parse(Rule::program, source)?;
    for pair in pairs.clone() {
        recursive_print(Some(&pair), 0);
    }

    for pair in pairs {
        match pair.as_rule() {
            Rule::fun_dec => {
                ast.push(build_ast_from_fun_dec(pair));
            }
            _ => {}
        }
    }

    Ok(ast)
}

macro_rules! fields {
    ($pair:ident |> $last:ident) => {
        let $last = $pair.next().unwrap();
    };

    ($pair:ident |> $first:ident $(, $tail:ident)*) => {
        let $first = $pair.next().unwrap();
        fields!($pair |> $($tail),*);
    };
}

fn build_ast_from_fun_dec(pair: Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::fun_dec => {
            let mut pair = pair.into_inner();
            fields!(pair |> name, args);
            let name = build_ast_from_expr(name);
        }
        unknown_expr => panic!("Expected function declaration, got: {:?}", unknown_expr),
    }
}

fn build_ast_from_expr(pair: Pair<Rule>) -> Result<Expr, Error<String>> {
    match pair.as_rule() {
        Rule::ident => Ok(Expr::Ident(pair.as_span().as_str().to_owned())),
        Rule::string => Ok(Expr::String(pair.as_span().as_str().to_owned())),
        Rule::number => Ok(Expr::Number(
            pair.as_span()
                .as_str()
                .parse::<f32>()
                .expect("Failed to parse number"),
        )),
        Rule::call => {
            let mut pair = pair.into_inner();
            fields!(pair |> name, args);

            let args = args
                .into_inner()
                .map(|pair| build_ast_from_expr(pair).expect("Failed to parse call args"))
                .collect();

            if let Ok(Expr::Ident(name)) = build_ast_from_expr(name) {
                Ok(Expr::Call { name, args })
            } else {
                panic!("Expected identifier, got: {:?}", name);
            }
        },
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn build_name_from_pair(pair: Pair<Rule>) -> Result<String, Error<String>> {

}

fn recursive_print(cur: Option<&Pair<Rule>>, depth: u8) {
    if let Some(node) = cur {
        let rule = node.as_rule();
        let rule_space = (0..(format!("{rule:?}").len()
            + if rule == Rule::fun_dec { 2 } else { 0 }))
            .map(|_| " ")
            .collect::<String>();

        let indent = (0..depth)
            .map(|_| "\x1b[32m|   \x1b[0m")
            .collect::<String>();

        println!(
            "{}\x1b[1;33m{:?}\x1b[0m:'{}'",
            indent,
            rule,
            node.as_span()
                .as_str()
                .lines()
                .map(|line| line.trim())
                .collect::<String>() // .replace('\n', format!("\n{indent}{rule_space}").as_ref()),
        );

        for pair in node.clone().into_inner() {
            recursive_print(Some(&pair), depth + 1);
        }
    }
}

fn main() {
    let unparsed_file =
        std::fs::read_to_string("examples/hello_world.tst").expect("cannot read tst file");
    let astnode = parse(&unparsed_file).expect("unsuccessful parse");
}
