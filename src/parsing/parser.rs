use pest::iterators::Pair;
use pest::Parser;
use pest_derive::Parser;
use crate::parsing::equation_datastructure::{Equation, EquationKind, OPBFile, Summand};

#[derive(Parser)]
#[grammar = "./src/parsing/opb.pest"] // points to the grammar file we created
struct OPBParser;

pub fn parse(content: &str) -> Result<OPBFile, String>{
    let opb_file = OPBParser::parse(Rule::opb_file, content);
    match opb_file {
        Ok(mut o) => {
            match o.next() {
                None => {
                    Err("Parsing error! Empty File.".to_string())
                },
                Some(t) => {
                    parse_opb_file(t)
                }
            }
        },
        Err(e) => {
            Err(format!("Parsing error! {}", e.to_string()))
        }
    }
}

fn parse_opb_file(rule: Pair<Rule>) -> Result<OPBFile, String> {
    let mut opb_file = OPBFile::new();

    for inner_rule in rule.into_inner(){
        match inner_rule.as_rule() {
            Rule::equation=> {
                let equation = parse_equation(inner_rule, &mut opb_file);
                match equation {
                    Ok(o) => {
                        opb_file.equations.push(o);
                    },
                    Err(e) => return Err(e)
                }
            },
            Rule::header=> {
                parse_header(inner_rule, &mut opb_file);
            }
            Rule::EOI => (),
            _ => return Err(format!("Parsing error! {} is not part of a valid opb file", inner_rule.as_str()))
        }
    }
    Ok(opb_file)
}

fn parse_header(rule: Pair<Rule>, opb_file: &mut OPBFile) {
    for inner_rule in rule.into_inner(){
        match inner_rule.as_rule() {
            Rule::number_variables=> {
                opb_file.number_variables = inner_rule.as_str().trim().parse().unwrap();
            },
            Rule::number_constraints => {
                opb_file.number_constraints = inner_rule.as_str().trim().parse().unwrap();
            },
            _ => ()
        }
    }

}

fn parse_equation(rule: Pair<Rule>, opb_file: &mut OPBFile) -> Result<Equation, String> {
    let mut equation_side = None;
    let mut equation_kind = None;
    let mut rhs = None;
    let equation_string = rule.as_str();
    for inner_rule in rule.into_inner(){
        match inner_rule.as_rule() {
            Rule::equation_side=> {
                equation_side = Some(parse_equation_side(inner_rule, opb_file));
            }
            Rule::equation_kind => {
                equation_kind = Some(parse_equation_kind(inner_rule));
            }
            Rule::right_hand_side => {
                rhs = Some(parse_right_hand_side(inner_rule));
            },
            _ => return Err(format!("Parsing error! {} is not part of an equation", inner_rule.as_str()))
        }
    }

    match (equation_side, equation_kind, rhs){
        (Some(e), Some(k), Some(r)) => {
            Ok(Equation {
                lhs: e?,
                kind: k?,
                rhs: r?,
            })
        },
        _ => Err(format!("Parsing error! {} is not a complete equation", equation_string))
    }
}

fn parse_equation_side(rule: Pair<Rule>, opb_file: &mut OPBFile) -> Result<Vec<Summand>, String> {
    let mut equation_side= Vec::new();
    for inner_rule in rule.into_inner(){
        equation_side.push(parse_summand(inner_rule, opb_file));
    }

    equation_side.into_iter().collect()
}

fn parse_summand(rule: Pair<Rule>, opb_file: &mut OPBFile) -> Result<Summand, String> {
    let mut factor = 1;
    let mut sign = 1;
    let mut var_name = None;

    let summand_string = rule.as_str();

    for inner_rule in rule.into_inner(){
        match inner_rule.as_rule() {
            Rule::factor_value=> {
                factor = inner_rule.as_str().trim().parse().unwrap();
            }
            Rule::factor_sign => {
                if inner_rule.as_str().trim().eq("-") {
                    sign = -1;
                }
            }
            Rule::var_name => {
                var_name = Some(inner_rule.as_str());
            },
            _ => return Err(format!("Parsing error! {} is not a valid summand", inner_rule.as_str()))
        }
    }

    if let Some(v) = var_name {
        let result = opb_file.name_map.get_by_left(v);
        let var_index;
        if let Some(i) = result {
            var_index = *i;
        }else{
            var_index = opb_file.max_name_index;
            opb_file.max_name_index += 1;
            opb_file.name_map.insert(v.parse().unwrap(), var_index);
        };
        Ok(Summand {
            factor: factor * sign,
            variable_index: var_index,
            positive: true,
        })
    }else{
        Err(format!("Parsing error! {} is not a valid summand", summand_string))
    }
}

fn parse_right_hand_side(rule: Pair<Rule>) -> Result<i128, String> {
    let mut value: Option<i128> = None;
    let mut sign = 1;

    let rhs_string = rule.as_str();

    for inner_rule in rule.into_inner(){
        match inner_rule.as_rule() {
            Rule::factor_value=> {
                value = inner_rule.as_str().trim().parse().ok();
            }
            Rule::factor_sign => {
                match inner_rule.as_str().trim() {
                    "-" => sign = -1,
                    _ => ()
                }
            }
            _ => return Err(format!("Parsing error! {} is not a valid right hand side", inner_rule.as_str()))
        }
    }

    match value {
        Some(v) => Ok(sign * v),
        _ => Err(format!("Parsing error! {} is not a valid right hand side", rhs_string))
    }
}

fn parse_equation_kind(rule: Pair<Rule>) -> Result<EquationKind, String> {
    match rule.as_str() {
        "=" => Ok(EquationKind::Eq),
        "<=" => Ok(EquationKind::Le),
        ">=" => Ok(EquationKind::Ge),
        "<" => Ok(EquationKind::L),
        ">" => Ok(EquationKind::G),
        "!=" => Ok(EquationKind::NotEq),
        _ => Err(format!("Parsing error! {} is not an equation kind!", rule.as_str()))
    }
}

#[cfg(test)]
mod tests {
    use serial_test::serial;
    use crate::parsing;
    use super::*;

    #[test]
    fn test_ex_1() {
        let result = parsing::parser::parse("");

        match result {
            Err(err) => {
                assert_eq!(err, "Parsing error!  --> 1:1\n  |\n1 | \n  | ^---\n  |\n  = expected header".to_string());
            }
            Ok(_) => panic!("Expected an error, but got Ok instead."),
        }
    }

    #[test]
    fn test_ex_2() {
        let result = parsing::parser::parse("#variable= 0 #constraint= 0\n");

        match result {
            Err(err) => {
                assert_eq!(err, "Parsing error!  --> 2:1\n  |\n2 | \n  | ^---\n  |\n  = expected first_literal".to_string());
            }
            Ok(_) => panic!("Expected an error, but got Ok instead."),
        }
    }

    #[test]
    fn test_ex_3() {
        let result = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 * x2 >= 1");

        match result {
            Err(err) => {
                assert_eq!(err, "Parsing error!  --> 2:4\n  |\n2 | x1 * x2 >= 1\n  |    ^---\n  |\n  = expected factor_sign or equation_kind".to_string());
            }
            Ok(_) => panic!("Expected an error, but got Ok instead."),
        }
    }

    #[test]
    fn test_ex_4() {
        let result = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 _ 1;\n");

        match result {
            Err(err) => {
                assert_eq!(err, "Parsing error!  --> 2:9\n  |\n2 | x1 + x2 _ 1;\n  |         ^---\n  |\n  = expected factor_sign or equation_kind".to_string());
            }
            Ok(_) => panic!("Expected an error, but got Ok instead."),
        }
    }
}