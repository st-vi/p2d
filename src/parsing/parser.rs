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
            }
            Rule::EOI => (),
            _ => return Err(format!("Parsing error! {} is not part of a valid opb file", inner_rule.as_str()))
        }
    }
    Ok(opb_file)
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

fn parse_right_hand_side(rule: Pair<Rule>) -> Result<i32, String> {
    let mut value: Option<i32> = None;
    let mut sign:  i32 = 1;

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
        _ => Err(format!("Parsing error! {} is not an equation kind!", rule.as_str()))
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_parse() {
        let opb_file = parse("x1 + x2 - 3*x3 >= 7");
        if let Ok(o) = opb_file {
            assert_eq!(o.equations.len(), 1);
            let equations = o.equations.get(0).unwrap();
            assert_eq!(equations.rhs, 7);
            assert_eq!(equations.kind, EquationKind::Ge);
            assert_eq!(equations.lhs.len(), 3);
            let s1_index = o.name_map.get_by_left("x1").unwrap();
            assert_eq!(equations.lhs.get(0).unwrap().variable_index, *s1_index);
            assert_eq!(equations.lhs.get(0).unwrap().factor, 1);
            assert_eq!(equations.lhs.get(0).unwrap().positive, true);
            let s2_index = o.name_map.get_by_left("x2").unwrap();
            assert_eq!(equations.lhs.get(1).unwrap().variable_index, *s2_index);
            assert_eq!(equations.lhs.get(1).unwrap().factor, 1);
            assert_eq!(equations.lhs.get(1).unwrap().positive, true);
            let s3_index = o.name_map.get_by_left("x3").unwrap();
            assert_eq!(equations.lhs.get(2).unwrap().variable_index, *s3_index);
            assert_eq!(equations.lhs.get(2).unwrap().factor, -3);
            assert_eq!(equations.lhs.get(2).unwrap().positive, true);
        } else {
            assert!(false);
        }
    }
}