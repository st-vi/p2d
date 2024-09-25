use std::cmp::Ordering;
use std::collections::{HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use crate::parsing::equation_datastructure::{Equation, EquationKind, OPBFile, Summand};
use crate::parsing::equation_datastructure::EquationKind::{Eq, Le};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::{AlreadySatisfied, ImpliedLiteral, NothingToPropagated, Satisfied, Unsatisfied};

#[derive(Clone)]
pub struct PseudoBooleanFormula {
    pub constraints: Vec<Constraint>,
    pub number_variables: u32,
    pub constraints_by_variable: Vec<HashSet<usize>>
}
#[derive(Clone)]
pub struct Constraint {
    literals: Vec<Option<Literal>>,
    unassigned_literals: HashSet<Literal>,
    degree: i32,
    sum_true: u32,
    sum_unassigned: u32,
    assignments: HashSet<(u32, bool)>,
    factor_sum: u32,
    //TODO cashe sum of max literal and update when necessary instead of calculating every time
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct Literal {
    pub index: u32,
    pub factor: u32,
    pub positive: bool
}

pub enum PropagationResult {
    Satisfied,
    Unsatisfied,
    ImpliedLiteral(Literal),
    NothingToPropagated,
    AlreadySatisfied
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.factor.cmp(&other.factor)
    }
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
        let mut pseudo_boolean_formula = PseudoBooleanFormula{
            constraints: Vec::new(),
            number_variables: opb_file.max_name_index,
            constraints_by_variable: Vec::with_capacity((opb_file.max_name_index - 1)as usize)
        };

        for _ in 0..opb_file.max_name_index{
            pseudo_boolean_formula.constraints_by_variable.push(HashSet::new());
        }

        let mut constraint_counter = 0;
        for equation in equation_list {
            //TODO set rhs to 0 if it is negative
            let mut constraint = Constraint {
                degree: equation.rhs,
                sum_true: 0,
                sum_unassigned: equation.lhs.iter().map(|s| s.factor).sum::<i32>() as u32,
                literals: Vec::with_capacity((opb_file.max_name_index - 1) as usize),
                unassigned_literals: HashSet::new(),
                assignments: HashSet::new(),
                factor_sum: equation.lhs.iter().map(|s| s.factor).sum::<i32>() as u32
            };
            for _ in 0..opb_file.max_name_index{
                constraint.literals.push(None);
            }
            for summand in equation.lhs {
                constraint.literals[summand.variable_index as usize] = Some(Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u32,
                    positive: summand.positive});
                constraint.unassigned_literals.insert(Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u32,
                    positive: summand.positive});
                pseudo_boolean_formula.constraints_by_variable.get_mut(summand.variable_index as usize).unwrap().insert(constraint_counter);
            }
            pseudo_boolean_formula.constraints.push(constraint);
            constraint_counter += 1;
        }
        pseudo_boolean_formula
    }
}

impl Constraint {
    pub fn propagate(&mut self, literal: Literal) -> PropagationResult {
        if self.assignments.contains(&(literal.index, !literal.positive)) {
            return Unsatisfied
        }else if self.assignments.contains(&(literal.index, literal.positive)){
            return NothingToPropagated
        }
        let already_satisfied =  self.sum_true >= self.degree as u32;
        let literal_in_constraint = self.literals.get(literal.index as usize).unwrap();
        match literal_in_constraint {
            None => {
                panic!("Propagate must only be called on constraints that actually contain the literal!")
            },
            Some(literal_in_constraint) => {
                if literal_in_constraint.positive == literal.positive {
                    //literal factor is taken
                    self.sum_true += literal_in_constraint.factor;
                    self.sum_unassigned -= literal_in_constraint.factor;
                    self.unassigned_literals.retain(|x| x.index != literal.index);
                    self.assignments.insert((literal.index, literal.positive));
                }else{
                    //literal factor is not taken
                    self.sum_unassigned -= literal_in_constraint.factor;
                    self.unassigned_literals.retain(|x| x.index != literal.index);
                    self.assignments.insert((literal.index, literal.positive));
                }
                if self.sum_true >= self.degree as u32 {
                    // fulfilled
                    return if already_satisfied {
                        AlreadySatisfied
                    } else {
                        Satisfied
                    }

                }else if self.sum_true + self.sum_unassigned < self.degree as u32 {
                    // violated
                    self.unassigned_literals.retain(|x| x.index != literal.index);
                    self.assignments.insert((literal.index, literal.positive));
                    return Unsatisfied
                }else if self.sum_true + self.sum_unassigned < (self.degree as u32) + self.unassigned_literals.iter().max().unwrap().factor {
                    //max literal implied
                    let max_literal = self.unassigned_literals.iter().max().unwrap().clone();
                    let return_value = ImpliedLiteral(max_literal.clone());
                    return return_value;
                }
                NothingToPropagated

            }
        }
    }

    pub fn undo(&mut self, variable_index: u32, variable_sign: bool) -> bool {
        if let Some(literal) = self.literals.get(variable_index as usize).unwrap() {
            let satisfied_before_undo = self.sum_true >= self.degree as u32;
            self.unassigned_literals.insert(literal.clone());
            self.assignments.remove(&(variable_index, variable_sign));
            self.sum_unassigned += literal.factor;
            if literal.positive == variable_sign {
                self.sum_true -= literal.factor;
            }
            let satisfied_after_undo = self.sum_true >= self.degree as u32;
            if satisfied_before_undo && !satisfied_after_undo {
                return true;
            }
        }
        false
    }

    pub fn simplify(&mut self) -> PropagationResult {
        if self.sum_true >= self.degree as u32 {
            // fulfilled
                return Satisfied
        }else if self.sum_true + self.sum_unassigned < self.degree as u32 {
            // violated
            return Unsatisfied
        }else if self.sum_true + self.sum_unassigned < (self.degree as u32) + self.unassigned_literals.iter().max().unwrap().factor {
            //max literal implied
            let max_literal = self.unassigned_literals.iter().max().unwrap().clone();
            let return_value = ImpliedLiteral(max_literal.clone());
            self.unassigned_literals.remove(&max_literal);
            return return_value;
        }
        NothingToPropagated
    }

    pub fn is_unsatisfied(&self) -> bool {
        self.sum_true < self.degree as u32
    }

    pub fn hash(&self, x: &mut DefaultHasher) -> u64 {
        let mut s = DefaultHasher::new();
        self.literals.hash(&mut s);
        for item in &self.assignments {
            item.hash(&mut s);
        }
        for item in &self.unassigned_literals {
            item.hash(&mut s);
        }
        self.degree.hash(&mut s);
        s.finish()
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
        let opb_file = parse("-2 x1 = 7;\n1 x1 <= 1;\n2 x + 3 x + 1 x >= 3");
        if let Ok(o) = opb_file {
            let formula = PseudoBooleanFormula::new(&o);
            assert_eq!(formula.constraints.len(), 4);
            assert_eq!(formula.constraints.get(0).unwrap().degree, 9);
            assert_eq!(formula.constraints.get(0).unwrap().literals.get(0).unwrap().as_ref().unwrap().factor, 2);
            assert_eq!(formula.constraints.get(0).unwrap().literals.get(0).unwrap().as_ref().unwrap().positive, false);
            assert_eq!(formula.constraints.get(0).unwrap().sum_unassigned, 2);
            assert_eq!(formula.constraints.get(0).unwrap().sum_true, 0);
            assert_eq!(formula.constraints.get(1).unwrap().degree, -7);
            assert_eq!(formula.constraints.get(1).unwrap().literals.get(0).unwrap().as_ref().unwrap().factor, 2);
            assert_eq!(formula.constraints.get(1).unwrap().literals.get(0).unwrap().as_ref().unwrap().positive, true);
            assert_eq!(formula.constraints.get(1).unwrap().sum_unassigned, 2);
            assert_eq!(formula.constraints.get(1).unwrap().sum_true, 0);
            assert_eq!(formula.constraints.get(2).unwrap().degree, 0);
            assert_eq!(formula.constraints.get(2).unwrap().literals.get(0).unwrap().as_ref().unwrap().factor, 1);
            assert_eq!(formula.constraints.get(2).unwrap().literals.get(0).unwrap().as_ref().unwrap().positive, false);
            assert_eq!(formula.constraints.get(2).unwrap().sum_unassigned, 1);
            assert_eq!(formula.constraints.get(2).unwrap().sum_true, 0);
            assert_eq!(formula.constraints.get(3).unwrap().unassigned_literals.iter().max().unwrap().factor, 3);
        } else {
            assert!(false);
        }
    }
}