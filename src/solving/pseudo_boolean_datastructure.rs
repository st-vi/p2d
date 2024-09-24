use crate::parsing::equation_datastructure::{Equation, EquationKind, OPBFile, Summand};
use crate::parsing::equation_datastructure::EquationKind::{Eq, Le};

pub struct PseudoBooleanFormula {
    pub constraints: Vec<Constraint>,
}

pub struct Constraint {
    pub literals: Vec<Literal>,
    pub degree: i32,
}

pub struct Literal {
    pub index: u32,
    pub factor: u32,
    pub positive: bool
}

impl PseudoBooleanFormula {
    pub fn new(opb_file: &OPBFile) -> PseudoBooleanFormula {
        let mut equation_list: Vec<Equation> = opb_file.equations.iter().flat_map(|x| replace_equal_equations(x)).collect();
        equation_list = equation_list.iter().map(|x| replace_le_equations(x)).collect();
        equation_list = equation_list.iter().map(|x| replace_negative_factors(x)).collect();
        equation_list.iter()
            .for_each(|e|
                if e.lhs.iter().filter(|s| s.factor < 0).collect::<Vec<&Summand>>().len() > 0 {
                    panic!("Factors must be negative to create a PseudoBooleanFormula")
                }

            );
        PseudoBooleanFormula {
            constraints: equation_list.iter()
                .map(|e|
                    Constraint{
                        degree: e.rhs,
                        literals: e.lhs.iter()
                            .map(|s|
                                Literal{
                                    index: s.variable_index,
                                    factor: s.factor as u32,
                                    positive: s.positive})
                            .collect()})
                .collect()
        }
    }
}

fn replace_equal_equations(equation: &Equation) -> Vec<Equation> {
    if equation.kind == Eq {
        let e1 = Equation {
            lhs: equation.lhs.clone(),
            rhs: equation.rhs,
            kind: EquationKind::Ge,
        };
        let e2 = Equation {
            lhs: equation.lhs.clone(),
            rhs: equation.rhs,
            kind: EquationKind::Le,
        };
        vec![e1,e2]
    }else {
        vec![equation.clone()]
    }

}

fn replace_le_equations(equation: &Equation) -> Equation {
    if equation.kind == Le {
        let mut e = Equation{
            lhs: equation.lhs.clone(),
            rhs: -1* equation.rhs,
            kind: EquationKind::Ge
        };
        e.lhs = e.lhs.iter().map(|s| Summand{variable_index: s.variable_index, factor: -1 * s.factor, positive: s.positive}).collect();
        e
    } else {
        equation.clone()
    }
}

fn replace_negative_factors(equation: &Equation) -> Equation {
    let mut new_equation = Equation {
        lhs: Vec::new(),
        rhs: equation.rhs.clone(),
        kind: equation.kind.clone(),
    };
    for s in &equation.lhs {
        if s.factor < 0 {
            new_equation.lhs.push(
              Summand{
                  factor: -1*s.factor,
                  variable_index: s.variable_index,
                  positive: !s.positive
              }
            );
            new_equation.rhs -= s.factor;
        }else{
            new_equation.lhs.push(s.clone());
        }
    }
    new_equation
}

#[cfg(test)]
mod tests {
    use crate::parsing::parser::parse;
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn test_parse() {
        let opb_file = parse("-2 x1 = 7;\n1 x1 <= 1");
        if let Ok(o) = opb_file {
            let formula = PseudoBooleanFormula::new(&o);
            assert_eq!(formula.constraints.len(), 3);
            assert_eq!(formula.constraints.get(0).unwrap().degree, 9);
            assert_eq!(formula.constraints.get(0).unwrap().literals.get(0).unwrap().factor, 2);
            assert_eq!(formula.constraints.get(0).unwrap().literals.get(0).unwrap().positive, false);
            assert_eq!(formula.constraints.get(1).unwrap().degree, -7);
            assert_eq!(formula.constraints.get(1).unwrap().literals.get(0).unwrap().factor, 2);
            assert_eq!(formula.constraints.get(1).unwrap().literals.get(0).unwrap().positive, true);
            assert_eq!(formula.constraints.get(2).unwrap().degree, 0);
            assert_eq!(formula.constraints.get(2).unwrap().literals.get(0).unwrap().factor, 1);
            assert_eq!(formula.constraints.get(2).unwrap().literals.get(0).unwrap().positive, false);
        } else {
            assert!(false);
        }
    }
}