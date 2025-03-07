use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashSet};
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
    pub literals: BTreeMap<usize,Literal>,
    pub unassigned_literals: BTreeMap<usize, Literal>,
    pub degree: i128,
    pub sum_true: u128,
    pub sum_unassigned: u128,
    pub assignments: BTreeMap<usize, (bool,AssignmentKind,u32)>,
    pub factor_sum: u128,
    pub hash_value: u64,
    pub hash_value_old: bool,
    pub constraint_type: ConstraintType,
    pub max_literal: Literal,
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
    pub factor: u128,
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
        equation_list = equation_list.iter().map(|x| add_up_same_variables(x)).collect();
        equation_list = equation_list.iter().map(|x| replace_negative_factors(x)).collect();
        equation_list.iter()
            .for_each(|e|
                if e.lhs.iter().filter(|s| s.factor < 0).collect::<Vec<&Summand>>().len() > 0 {
                    panic!("Factors must be negative to create a PseudoBooleanFormula")
                }

            );
        let mut pseudo_boolean_formula = PseudoBooleanFormula{
            constraints: Vec::with_capacity(opb_file.number_constraints),
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
                degree: if equation.rhs < 0 {0} else {equation.rhs},
                sum_true: 0,
                sum_unassigned: equation.lhs.iter().map(|s| s.factor).sum::<i128>() as u128,
                literals: BTreeMap::new(),
                unassigned_literals: BTreeMap::new(),
                assignments: BTreeMap::new(),
                factor_sum: equation.lhs.iter().map(|s| s.factor).sum::<i128>() as u128,
                index: NormalConstraintIndex(constraint_counter),
                hash_value: 0,
                hash_value_old: true,
                constraint_type: get_constraint_type_from_equation(&equation),
                max_literal: Literal{ index: 0, factor: 0, positive: false },
            };
            for summand in equation.lhs {
                constraint.literals.insert(summand.variable_index as usize, Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u128,
                    positive: summand.positive});
                constraint.unassigned_literals.insert(summand.variable_index as usize, Literal{
                    index: summand.variable_index,
                    factor: summand.factor as u128,
                    positive: summand.positive});
                pseudo_boolean_formula.constraints_by_variable.get_mut(summand.variable_index as usize).unwrap().push(constraint_counter as usize);
            }
            constraint.max_literal = constraint.get_max_literal();
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

        let already_satisfied =  if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u128 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u128};

        if already_satisfied {
            return AlreadySatisfied;
        }


        let literal_in_constraint = self.literals.get(&(literal.index as usize));
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
                    if self.sum_unassigned == 0 && self.sum_true != self.degree as u128 {
                        // fulfilled
                        return if already_satisfied {
                            AlreadySatisfied
                        } else {
                            Satisfied
                        }
                    }else if self.sum_unassigned == 0 && self.sum_true == self.degree as u128 {
                        // violated
                        return Unsatisfied
                    }else {
                        return NothingToPropagated
                    }
                }

                self.max_literal = self.get_max_literal();

                if self.sum_true >= self.degree as u128 {
                    // fulfilled
                    return if already_satisfied {
                        AlreadySatisfied
                    } else {
                        Satisfied
                    }

                }else if self.sum_true + self.sum_unassigned < self.degree as u128 {
                    // violated
                    return Unsatisfied
                }else if self.sum_true + self.sum_unassigned == self.degree as u128 {
                    let mut implied_literals = Vec::new();
                    for (index, unassigned_literal) in &self.unassigned_literals {
                        implied_literals.push(Literal{index: *index as u32, factor: unassigned_literal.factor, positive: unassigned_literal.positive});
                    }
                    return ImpliedLiteralList(implied_literals);
                } else {

                    if self.sum_true + self.sum_unassigned < (self.degree as u128) + self.max_literal.factor {
                        //max literal implied
                        let return_value = ImpliedLiteral(self.max_literal.clone());
                        return return_value;
                    }
                }
                NothingToPropagated

            }
        }
    }

    pub fn undo(&mut self, variable_index: u32, variable_sign: bool) -> bool {
        if self.assignments.contains_key(&(variable_index as usize)) {
            if let Some(literal) = self.literals.get(&(variable_index as usize)) {
                if literal.factor > self.max_literal.factor {
                    self.max_literal = literal.clone();
                }
                let satisfied_before_undo = if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u128 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u128};
                self.unassigned_literals.insert(literal.index as usize, literal.clone());
                self.assignments.remove(&(variable_index as usize));
                self.sum_unassigned += literal.factor;
                if literal.positive == variable_sign {
                    self.sum_true -= literal.factor;
                }
                let satisfied_after_undo = if self.constraint_type == GreaterEqual { self.sum_true >= self.degree as u128 } else {self.sum_unassigned == 0 && self.sum_true != self.degree as u128};
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
            if self.sum_unassigned == 0 && self.sum_true != self.degree as u128 {
                // fulfilled
                return Satisfied
            }else if self.sum_unassigned == 0 && self.sum_true == self.degree as u128 {
                // violated
                return Unsatisfied
            }else {
                return NothingToPropagated
            }
        }

        if self.sum_true >= self.degree as u128 {
            // fulfilled
                return Satisfied
        }else if self.sum_true + self.sum_unassigned < self.degree as u128 {
            // violated
            return Unsatisfied
        }else if self.sum_true + self.sum_unassigned == self.degree as u128 {
            let mut implied_literals = Vec::new();
            for (index, unassigned_literal) in &self.unassigned_literals {
                implied_literals.push(Literal{index: *index as u32, factor: unassigned_literal.factor, positive: unassigned_literal.positive});
            }
            return ImpliedLiteralList(implied_literals);
        }else{
            if self.sum_true + self.sum_unassigned < (self.degree as u128) + self.max_literal.factor {
                //max literal implied
                let return_value = ImpliedLiteral(self.max_literal.clone());
                return return_value;
            }
        }
        NothingToPropagated
    }

    pub fn is_unsatisfied(&self) -> bool {
        if self.constraint_type == GreaterEqual {
            self.sum_true < self.degree as u128
        } else {
            self.sum_unassigned != 0 || self.sum_true == self.degree as u128
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

    pub fn get_max_literal(&self) -> Literal {
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
        Literal{index: max_literal_index, factor: max_literal_factor, positive: max_literal_sign}
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
        let e = Equation{
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

fn add_up_same_variables(equation: &Equation) -> Equation {
    let mut new_equation = Equation {
        lhs: Vec::new(),
        rhs: equation.rhs.clone(),
        kind: equation.kind.clone(),
    };

    let mut visited = HashSet::new();

    for i in 0..equation.lhs.len() {
        if visited.contains(&equation.lhs.get(i).unwrap().variable_index) {
            continue;
        }else{
            visited.insert(equation.lhs.get(i).unwrap().variable_index);
        }
        let current_equation = equation.lhs.get(i).unwrap();
        let mut summand = Summand{
            factor: current_equation.factor,
            variable_index: current_equation.variable_index,
            positive: current_equation.positive
        };

        for j in i+1..equation.lhs.len() {
            if summand.variable_index == equation.lhs.get(j).unwrap().variable_index {
                summand.factor += equation.lhs.get(j).unwrap().factor;
            }
        }
        new_equation.lhs.push(summand)
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

pub fn calculate_hash(variables_in_scope: & BTreeSet<usize>, assigments: &Vec<Option<(u32, bool)>>, t: &mut PseudoBooleanFormula, n: u32, constraint_indexes_in_scope: &BTreeSet<usize>) -> u64 {
    let mut s = DefaultHasher::new();

    variables_in_scope.hash(&mut s);
    '|'.hash(&mut s);
    for ci in constraint_indexes_in_scope {
        (ci, t.constraints.get(*ci).unwrap().sum_true).hash(&mut s);
    }

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

            self.hash_value = s.finish();
            self.hash_value_old = false;

        }
        self.hash_value
    }
}