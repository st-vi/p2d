use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use bimap::BiMap;
use crate::parsing::equation_datastructure::{Equation, EquationKind, OPBFile, Summand};
use crate::parsing::equation_datastructure::EquationKind::{Eq, Le, G, L};
use crate::solving::pseudo_boolean_datastructure::ConstraintIndex::NormalConstraintIndex;
use crate::solving::pseudo_boolean_datastructure::ConstraintType::{GreaterEqual, NotEqual};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::{AlreadySatisfied, ImpliedLiteral, ImpliedLiteralList, NothingToPropagated, Satisfied, Unsatisfied};
use crate::solving::solver::AssignmentKind;

#[derive(Clone,Debug,Eq, PartialEq)]
pub struct PseudoBooleanFormula {
    pub constraints: Vec<Constraint>,
    pub number_variables: u32,
    pub constraints_by_variable: Vec<Vec<usize>>,
    pub name_map: BiMap<String, u32>,
}
#[derive(Clone,Debug,Eq, PartialEq)]
pub struct Constraint {
    pub index: ConstraintIndex,
    pub literals: Vec<Option<Literal>>,
    pub unassigned_literals: BTreeMap<usize, Literal>,
    pub degree: i32,
    pub sum_true: u32,
    pub sum_unassigned: u32,
    pub assignments: BTreeMap<usize, (bool,AssignmentKind,u32)>,
    pub factor_sum: u32,
    pub hash_value: u64,
    pub hash_value_old: bool,
    pub constraint_type: ConstraintType,
    //TODO cashe sum of max literal and update when necessary instead of calculating every time
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ConstraintType {
    GreaterEqual,
    NotEqual
}

fn get_constraint_type_from_equation(equation: &Equation) -> ConstraintType {
    match equation.kind {
        EquationKind::Ge => GreaterEqual,
        EquationKind::NotEq => NotEqual,
        _ => panic!("{:?} must be removed before creating a pseudo boolean constraint", equation.kind)
    }
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
    ImpliedLiteralList(Vec<Literal>),
    NothingToPropagated,
    AlreadySatisfied,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum ConstraintIndex {
    LearnedClauseIndex(usize),
    NormalConstraintIndex(usize)
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
        equation_list = equation_list.iter().map(|x| replace_l_equations(x)).collect();
        equation_list = equation_list.iter().map(|x| replace_g_equations(x)).collect();
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
            constraints_by_variable: Vec::with_capacity((opb_file.max_name_index - 1)as usize),
            name_map: opb_file.name_map.clone()
        };

        for _ in 0..opb_file.max_name_index{
            pseudo_boolean_formula.constraints_by_variable.push(Vec::new());
        }

        let mut constraint_counter = 0;
        for equation in equation_list {
            let mut constraint = Constraint {
                degree: equation.rhs,
                sum_true: 0,
                sum_unassigned: equation.lhs.iter().map(|s| s.factor).sum::<i32>() as u32,
                literals: Vec::with_capacity((opb_file.max_name_index - 1) as usize),
                unassigned_literals: BTreeMap::new(),
                assignments: BTreeMap::new(),
                factor_sum: equation.lhs.iter().map(|s| s.factor).sum::<i32>() as u32,
                index: NormalConstraintIndex(constraint_counter),
                hash_value: 0,
                hash_value_old: true,
                constraint_type: get_constraint_type_from_equation(&equation),
            };
            for _ in 0..opb_file.max_name_index{
                constraint.literals.push(None);
            }
            for summand in equation.lhs {
                constraint.literals[summand.variable_index as usize] = Some(Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u32,
                    positive: summand.positive});
                constraint.unassigned_literals.insert(summand.variable_index as usize, Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u32,
                    positive: summand.positive});
                pseudo_boolean_formula.constraints_by_variable.get_mut(summand.variable_index as usize).unwrap().push(constraint_counter as usize);
            }
            pseudo_boolean_formula.constraints.push(constraint);
            constraint_counter += 1;
        }
        pseudo_boolean_formula
    }
}

impl Constraint {
    pub fn propagate(&mut self, literal: Literal, assignment_kind: AssignmentKind, decision_level: u32) -> PropagationResult {
        if let Some((a,_,_)) = self.assignments.get(&(literal.index as usize)) {
            if *a == literal.positive {
                return NothingToPropagated;
            }else {
                println!("2");
                return Unsatisfied
            }
        }

        /*
        if self.assignments.contains(&(literal.index, !literal.positive)) {
            return Unsatisfied
        }else if self.assignments.contains(&(literal.index, literal.positive)){
            return NothingToPropagated
        }

         */
        let already_satisfied =  if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u32 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u32};
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
                    self.unassigned_literals.remove(&(literal.index as usize));
                    self.assignments.insert(literal.index as usize, (literal.positive, assignment_kind, decision_level));
                }else{
                    //literal factor is not taken
                    self.sum_unassigned -= literal_in_constraint.factor;
                    self.unassigned_literals.remove(&(literal.index as usize));
                    self.assignments.insert(literal.index as usize, (literal.positive, assignment_kind, decision_level));
                }
                self.hash_value_old = true;
                if self.constraint_type == NotEqual {
                    if self.sum_unassigned == 0 && self.sum_true != self.degree as u32 {
                        // fulfilled
                        return if already_satisfied {
                            AlreadySatisfied
                        } else {
                            Satisfied
                        }
                    }else if self.sum_unassigned == 0 && self.sum_true == self.degree as u32 {
                        // violated
                        return Unsatisfied
                    }else {
                        return NothingToPropagated
                    }
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
                    return Unsatisfied
                }else if self.sum_true + self.sum_unassigned == self.degree as u32 {
                    let mut implied_literals = Vec::new();
                    for (index, unassigned_literal) in &self.unassigned_literals {
                        implied_literals.push(Literal{index: *index as u32, factor: unassigned_literal.factor, positive: unassigned_literal.positive});
                    }
                    return ImpliedLiteralList(implied_literals);
                } else {
                    let mut max_literal_factor = 0;
                    let mut max_literal_index = 0;
                    let mut max_literal_sign = false;
                    for (_,literal) in &self.unassigned_literals {
                        if literal.factor > max_literal_factor {
                            max_literal_factor = literal.factor;
                            max_literal_index = literal.index;
                            max_literal_sign = literal.positive;
                        }

                    }
                    if self.sum_true + self.sum_unassigned < (self.degree as u32) + max_literal_factor {
                        //max literal implied
                        let return_value = ImpliedLiteral(Literal{index: max_literal_index, factor: max_literal_factor, positive: max_literal_sign});
                        return return_value;
                    }
                }
                NothingToPropagated

            }
        }
    }

    pub fn undo(&mut self, variable_index: u32, variable_sign: bool) -> bool {
        if self.assignments.contains_key(&(variable_index as usize)) {
            if let Some(literal) = self.literals.get(variable_index as usize).unwrap() {

                let satisfied_before_undo = if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u32 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u32};
                self.unassigned_literals.insert(literal.index as usize, literal.clone());
                self.assignments.remove(&(variable_index as usize));
                self.sum_unassigned += literal.factor;
                if literal.positive == variable_sign {
                    self.sum_true -= literal.factor;
                }
                let satisfied_after_undo = if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u32 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u32};
                self.hash_value_old = true;
                if satisfied_before_undo && !satisfied_after_undo {
                    return true;
                }
            }
        }

        false
    }

    pub fn simplify(&mut self) -> PropagationResult {
        if self.constraint_type == NotEqual {
            if self.sum_unassigned == 0 && self.sum_true != self.degree as u32 {
                // fulfilled
                return Satisfied
            }else if self.sum_unassigned == 0 && self.sum_true == self.degree as u32 {
                // violated
                return Unsatisfied
            }else {
                return NothingToPropagated
            }
        }

        if self.sum_true >= self.degree as u32 {
            // fulfilled
                return Satisfied
        }else if self.sum_true + self.sum_unassigned < self.degree as u32 {
            // violated
            return Unsatisfied
        }else if self.sum_true + self.sum_unassigned == self.degree as u32 {
            let mut implied_literals = Vec::new();
            for (index, unassigned_literal) in &self.unassigned_literals {
                implied_literals.push(Literal{index: *index as u32, factor: unassigned_literal.factor, positive: unassigned_literal.positive});
            }
            return ImpliedLiteralList(implied_literals);
        }else{
            let mut max_literal_factor = 0;
            let mut max_literal_index = 0;
            let mut max_literal_sign = false;
            for (_,literal) in &self.unassigned_literals {
                if literal.factor > max_literal_factor {
                    max_literal_factor = literal.factor;
                    max_literal_index = literal.index;
                    max_literal_sign = literal.positive;
                }
            }
            if max_literal_factor == 0{
                println!("test");
            }
            if self.sum_true + self.sum_unassigned < (self.degree as u32) + max_literal_factor {
                //max literal implied
                let return_value = ImpliedLiteral(Literal{index: max_literal_index, factor: max_literal_factor, positive: max_literal_sign});
                return return_value;
            }
        }
        NothingToPropagated
    }

    pub fn is_unsatisfied(&self) -> bool {
        if self.constraint_type == GreaterEqual {
            self.sum_true < self.degree as u32
        } else {
            self.sum_unassigned != 0 || self.sum_true == self.degree as u32
        }
    }

    pub fn calculate_reason(&self, propagated_variable_index: usize) -> BTreeMap<usize, (AssignmentKind,bool,u32)> {
        let mut result = BTreeMap::new();
        for (index, (sign,kind,decision_level)) in &self.assignments {
            if *index != propagated_variable_index {
                result.insert(*index, (*kind,*sign,*decision_level));
            }
        }
        result
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

fn replace_l_equations(equation: &Equation) -> Equation {
    if equation.kind == L {
        let mut e = Equation{
            lhs: equation.lhs.clone(),
            rhs: -1* equation.rhs,
            kind: EquationKind::G
        };
        e.lhs = e.lhs.iter().map(|s| Summand{variable_index: s.variable_index, factor: -1 * s.factor, positive: s.positive}).collect();
        e
    } else {
        equation.clone()
    }
}

fn replace_g_equations(equation: &Equation) -> Equation {
    if equation.kind == G {
        let mut e = Equation{
            lhs: equation.lhs.clone(),
            rhs: equation.rhs + 1,
            kind: EquationKind::Ge
        };
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

impl PseudoBooleanFormula {
    fn hash<H: Hasher>(&mut self, state: &mut H, constraints_in_scope: &BTreeSet<usize>) {

        for ci in constraints_in_scope {
            let constraint = self.constraints.get_mut(*ci).unwrap();
            if constraint.is_unsatisfied(){
                constraint.calculate_hash().hash(state);
            }
        }
    }
}

pub fn calculate_hash(t: &mut PseudoBooleanFormula, n: u32, constraint_indexes_in_scope: &BTreeSet<usize>) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s, constraint_indexes_in_scope);
    n.hash(&mut s);
    s.finish()
}


impl Constraint {
    fn calculate_hash(&mut self) -> u64 {
        if self.hash_value_old {
            let mut s = DefaultHasher::new();
            self.degree.hash(&mut s);
            self.constraint_type.hash(&mut s);
            self.unassigned_literals.hash(&mut s);
            self.sum_true.hash(&mut s);
            s.finish()
        }else{
            self.hash_value
        }
        //self.assignments.hash(state);
        //for (a,(b,_,_)) in &self.assignments {
            //(a,b).hash(state);
        //}

    }
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
        } else {
            assert!(false);
        }
    }
}