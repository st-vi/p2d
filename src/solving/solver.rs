use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{DefaultHasher, Hash, Hasher};
use crate::solving::pseudo_boolean_datastructure::{Constraint, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::solver::AssignmentKind::{FirstDecision, Propagated, SecondDecision};

pub struct Solver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<Assignment>,
    decision_level: u32,
    learned_clauses: Vec<Constraint>,
    result_stack: Vec<u128>,
    number_unsat_constraints: usize,
    unassigned_variables: HashSet<u32>,
    model_counter: u128,
    cache: HashMap<u64,(u128,PseudoBooleanFormula)>,
}

impl Solver {
    pub fn new(pseudo_boolean_formula: PseudoBooleanFormula) -> Solver {
        let number_unsat_constraints = pseudo_boolean_formula.constraints.len();
        let mut unassigned_variables = HashSet::new();
        for i in 0..pseudo_boolean_formula.number_variables{
            unassigned_variables.insert(i);
        }
        Solver {
            pseudo_boolean_formula,
            assignment_stack: Vec::new(),
            decision_level: 0,
            learned_clauses: Vec::new(),
            result_stack: Vec::new(),
            number_unsat_constraints,
            unassigned_variables,
            model_counter: 0,
            cache: HashMap::new()
        }
    }

    pub fn solve(&mut self) -> u128 {
        if !self.simplify(){
            return 0;
        }
        loop {
            if self.number_unsat_constraints <= 0 {
                self.result_stack.push(2_u128.pow(self.unassigned_variables.len() as u32));
                self.model_counter += 2_u128.pow(self.unassigned_variables.len() as u32);
                if !self.backtrack(){
                    //nothing to backtrack to, we searched the whole space
                    return self.result_stack.pop().unwrap();
                }
                continue
            }
            let cached_result = self.get_cached_result();
            match cached_result {
                None => {
                    self.decide();
                    let last_assignment = self.assignment_stack.last().unwrap();
                    if !self.propagate(last_assignment.variable_index, last_assignment.variable_sign){
                        //at least one constraint violated
                        self.result_stack.push(0);
                        if !self.backtrack(){
                            //nothing to backtrack to, we searched the whole space
                            return self.result_stack.pop().unwrap();
                        }
                    }
                },
                Some(c) => {
                    self.result_stack.push(c);
                    self.model_counter += c;
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return self.model_counter;
                    }
                    continue
                }
            }

        }
    }

    fn propagate(&mut self, variable_index: u32, variable_sign: bool) -> bool {
        let mut propagation_queue:VecDeque<(u32, bool)> = VecDeque::new();
        propagation_queue.push_back((variable_index, variable_sign));
        while !propagation_queue.is_empty() {
            let (index, sign) = propagation_queue.pop_front().unwrap();
            self.unassigned_variables.remove(&index);
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(index as usize).unwrap() {
                let result = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap().propagate(Literal{index, positive: sign, factor: 0});
                match result {
                    Satisfied => {
                        self.number_unsat_constraints -= 1;
                    },
                    Unsatisfied => {
                        propagation_queue.clear();
                        return false;
                    },
                    ImpliedLiteral(l) => {
                        let assignment = Assignment{
                            variable_sign: l.positive,
                            variable_index: l.index,
                            decision_level: self.decision_level,
                            assignment_kind: Propagated
                        };
                        propagation_queue.push_back((l.index, l.positive));
                        self.assignment_stack.push(assignment);
                    },
                    NothingToPropagated => {},
                    AlreadySatisfied => {}
                }
            }
        }
        true
    }

    fn decide(&mut self){
        self.decision_level += 1;
        //TODO better heuristic than smallest index?
        let variable_index = *self.unassigned_variables.iter().min().unwrap();
        self.unassigned_variables.remove(&variable_index);
        self.assignment_stack.push(Assignment{
            assignment_kind: AssignmentKind::FirstDecision,
            variable_sign: true,
            decision_level: self.decision_level,
            variable_index
        });
    }

    fn backtrack(&mut self) -> bool {
        loop {
            if let Some(top_element) = self.assignment_stack.last(){
                if top_element.decision_level == 0{
                    return false;
                }else if top_element.assignment_kind == Propagated {
                    self.undo_assignment(top_element.variable_index, top_element.variable_sign);
                    self.assignment_stack.pop();
                }else if top_element.assignment_kind == FirstDecision {
                    self.undo_assignment(top_element.variable_index, top_element.variable_sign);
                    let new_sign = !self.assignment_stack.last().unwrap().variable_sign;
                    self.assignment_stack.last_mut().unwrap().variable_sign = new_sign;
                    self.assignment_stack.last_mut().unwrap().assignment_kind = SecondDecision;
                    self.decision_level = self.assignment_stack.last_mut().unwrap().decision_level;
                    let last_assignment = self.assignment_stack.last().unwrap();
                    self.propagate(last_assignment.variable_index, last_assignment.variable_sign);
                    return true;
                }else if top_element.assignment_kind == SecondDecision {
                    let r1 = self.result_stack.pop().unwrap();
                    let r2 = self.result_stack.pop().unwrap();
                    self.result_stack.push(r1+r2);
                    let top_index = top_element.variable_index;
                    let top_sign = top_element.variable_sign;
                    self.undo_assignment(top_index, top_sign);
                    self.assignment_stack.pop();
                    self.cache();
                }
            }else {
                return false;
            }

        }
    }

    fn undo_assignment(&mut self, variable_index: u32, variable_sign: bool) {
        self.unassigned_variables.insert(variable_index);
        for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(variable_index as usize).unwrap() {
            let constraint = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap();
            if constraint.undo(variable_index, variable_sign) {
                self.number_unsat_constraints += 1;
            }
        }
    }

    fn simplify(&mut self) -> bool {
        let mut propagation_set = HashSet::new();
        for constraint in &mut self.pseudo_boolean_formula.constraints {
            match constraint.simplify(){
                Satisfied => {
                    self.number_unsat_constraints -= 1;
                },
                Unsatisfied => {
                    return false;
                },
                ImpliedLiteral(l) => {
                    self.assignment_stack.push(Assignment{
                        variable_index: l.index,
                        assignment_kind: Propagated,
                        decision_level: 0,
                        variable_sign: l.positive,
                    });
                    propagation_set.insert((l.index, l.positive));
                }
                _ => {}
            }
        }
        for (index, sign) in propagation_set {
            if !self.propagate(index, sign){
                return false;
            }
        }
        true
    }

    fn hash_state(&self) -> u64 {
        let mut s = DefaultHasher::new();

        for c in &self.pseudo_boolean_formula.constraints {
            if c.is_unsatisfied() {
                c.hash(&mut s);
            }
        }

        s.finish()
    }

    fn cache(&mut self) {
        if self.number_unsat_constraints > 0 {
            self.cache.insert(self.hash_state(), (*self.result_stack.last().unwrap(), self.pseudo_boolean_formula.clone()));
        }
    }

    fn get_cached_result(&self) -> Option<u128> {
        match self.cache.get(&self.hash_state()) {
            None => None,
            Some((c,_)) => Some(*c)
        }
    }
}

struct Assignment {
    decision_level: u32,
    variable_index: u32,
    variable_sign: bool,
    assignment_kind: AssignmentKind
}

#[derive(PartialEq)]
enum AssignmentKind {
    Propagated,
    FirstDecision,
    SecondDecision
}

#[cfg(test)]
mod tests {
    use crate::parsing;
    use super::*;

    #[test]
    fn test_ex_1() {
        let opb_file = parsing::parser::parse("x1 + x2 >= 0;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 18);
    }

    #[test]
    fn test_ex_2() {
        let opb_file = parsing::parser::parse("x1 + x2 >= 1;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 17);
    }
}