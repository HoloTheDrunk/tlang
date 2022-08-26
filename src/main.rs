extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::{
    error::{Error, ErrorVariant, LineColLocation},
    iterators::{Pair, Pairs},
    Parser,
};

struct ErrorTrace {
    stack: Vec<Error<Rule>>,
}

impl From<Error<Rule>> for ErrorTrace {
    fn from(err: Error<Rule>) -> Self {
        ErrorTrace { stack: vec![err] }
    }
}

impl std::fmt::Display for ErrorTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "Deepest error first\n{}",
            self.stack
                .iter()
                .map(|err| {
                    format!(
                        "--> {}\n{}\n |{}\n = {}\n",
                        match err.line_col {
                            LineColLocation::Pos((y, x)) => format!("{y}:{x}"),
                            LineColLocation::Span((ys, xs), (ye, xe)) =>
                                format!("{ys}:{xs} -> {ye}:{xe}"),
                        },
                        format_args!(
                            " |\n{}| {}",
                            match err.line_col {
                                LineColLocation::Pos((y, _)) => y,
                                LineColLocation::Span((ys, _), _) => ys,
                            },
                            err.line()
                        ),
                        match err.line_col {
                            LineColLocation::Pos((_, x)) =>
                                format!("{}^", (0..(x)).map(|_| " ").collect::<String>()),
                            LineColLocation::Span((ys, xs), (ye, xe)) =>
                                if ys == ye {
                                    format!(
                                        "{}^{}^",
                                        (0..(xs)).map(|_| " ").collect::<String>(),
                                        (0..(xe - xs - 1)).map(|_| "-").collect::<String>()
                                    )
                                } else {
                                    format!(
                                        "{}^{}",
                                        (0..(xs)).map(|_| " ").collect::<String>(),
                                        (0..(err.line().len() - xs))
                                            .map(|_| "-")
                                            .collect::<String>()
                                    )
                                },
                        },
                        err.variant.message()
                    )
                })
                .collect::<String>(),
        )
    }
}

impl ErrorTrace {
    fn push(&mut self, err: Error<Rule>) {
        self.stack.push(err)
    }
}

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
        body: Vec<Statement>,
    },
    Expr(Expr),
    Return(Expr),
}

fn parse(source: &str) -> Result<Vec<Statement>, ErrorTrace> {
    let mut ast = vec![];

    let pairs: Pairs<Rule> = TParser::parse(Rule::program, source)?;
    for pair in pairs.clone() {
        recursive_print(Some(&pair), 0);
    }

    for pair in pairs {
        match pair.as_rule() {
            Rule::fun_dec => ast.push(build_ast_from_statement(pair)?),
            Rule::EOI => {}
            unknown_rule => Err(Error::new_from_span(
                ErrorVariant::CustomError {
                    message: format!("Unknown rule: {:?}", unknown_rule),
                },
                pair.as_span(),
            ))?,
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

/// Pushes new error onto stacktrace or returns pred(pair).
fn handle<F, T>(parent: &Pair<Rule>, pair: Pair<Rule>, pred: F) -> Result<T, ErrorTrace>
where
    F: FnOnce(Pair<Rule>) -> Result<T, ErrorTrace>,
{
    let (span, rule) = (parent.as_span(), parent.as_rule());
    pred(pair).map_err(|mut trace| {
        trace.push(Error::new_from_span(
            ErrorVariant::ParsingError {
                positives: vec![rule],
                negatives: vec![],
            },
            span,
        ));
        trace
    })
}

// Builds [Statement] from either statement or expr rules
fn dispatch(pair: Pair<Rule>) -> Result<Statement, ErrorTrace> {
    match pair.as_rule() {
        Rule::fun_dec | Rule::var_dec | Rule::ret => build_ast_from_statement(pair),
        Rule::ident | Rule::string | Rule::number | Rule::call => {
            Ok(Statement::Expr(build_ast_from_expr(pair)?))
        }
        unknown => Err(Error::new_from_span(
            ErrorVariant::CustomError {
                message: format!("Unknown rule {:?}", unknown),
            },
            pair.as_span(),
        )
        .into()),
    }
}

fn build_ast_from_expr(pair: Pair<Rule>) -> Result<Expr, ErrorTrace> {
    match pair.as_rule() {
        Rule::ident => Ok(Expr::Ident(pair.as_str().to_owned())),
        Rule::string => Ok(Expr::String(pair.as_str().to_owned())),
        Rule::number => Ok(Expr::Number(
            pair.as_span()
                .as_str()
                .parse::<f32>()
                .expect("Failed to parse number"),
        )),
        Rule::call => {
            let mut children = pair.clone().into_inner();
            fields!(children |> name, args);

            let args = args
                .into_inner()
                .map(|child| handle(&pair, child, build_ast_from_expr))
                .collect::<Result<Vec<Expr>, ErrorTrace>>()?;

            if let Ok(Expr::Ident(name)) = build_ast_from_expr(name.clone()) {
                Ok(Expr::Call { name, args })
            } else {
                panic!("Expected identifier, got: {:?}", name);
            }
        }
        unknown_expr => panic!("Unexpected expression: {:?}", unknown_expr),
    }
}

fn build_ast_from_statement(pair: Pair<Rule>) -> Result<Statement, ErrorTrace> {
    match pair.as_rule() {
        Rule::fun_dec => {
            let span = pair.as_span();
            let mut children = pair.clone().into_inner();
            fields!(children |> name, args, body);

            let args = args
                .into_inner()
                .map(|pair| {
                    if let Ok(Expr::Ident(arg)) = build_ast_from_expr(pair) {
                        Ok(arg)
                    } else {
                        Err(Error::new_from_span(
                            ErrorVariant::ParsingError {
                                positives: vec![Rule::fun_dec],
                                negatives: vec![],
                            },
                            span,
                        )
                        .into())
                    }
                })
                .collect::<Result<Vec<String>, ErrorTrace>>()?;

            let body = body
                .into_inner()
                .map(|child| handle(&pair, child, dispatch))
                .collect::<Result<Vec<Statement>, ErrorTrace>>()?;

            if let Ok(Expr::Ident(name)) = build_ast_from_expr(name.clone()) {
                Ok(Statement::FunDec { name, args, body })
            } else {
                panic!("Expected identifier, got: {:?}", name);
            }
        }

        Rule::var_dec => {
            let span = pair.as_span();
            let mut children = pair.into_inner();
            fields!(children |> name, expr);

            let expr = build_ast_from_expr(expr)?;

            if let Expr::Ident(name) = build_ast_from_expr(name.clone())? {
                Ok(Statement::VarDec { name, expr })
            } else {
                Err(Error::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![Rule::var_dec, Rule::ident],
                        negatives: vec![],
                    },
                    span,
                )
                .into())
            }
        }

        Rule::ret => {
            let mut children = pair.into_inner();
            fields!(children |> expr);

            let expr = build_ast_from_expr(expr)?;

            Ok(Statement::Return(expr))
        }

        unknown_expr => Err(Error::new_from_span(
            ErrorVariant::CustomError {
                message: format!("unexpected statement: {:?}", unknown_expr),
            },
            pair.as_span(),
        )
        .into()),
    }
}

/* fn build_name_from_pair(pair: Pair<Rule>) -> Result<String, Error<String>> {

} */

fn recursive_print(cur: Option<&Pair<Rule>>, depth: u8) {
    if let Some(node) = cur {
        let rule = node.as_rule();
        /* let rule_space = (0..(format!("{rule:?}").len()
        + if rule == Rule::fun_dec { 2 } else { 0 }))
        .map(|_| " ")
        .collect::<String>(); */

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
    match parse(&unparsed_file) {
        Ok(ast) => println!("{:#?}", ast),
        Err(trace) => eprintln!("{}", trace),
    }
}
