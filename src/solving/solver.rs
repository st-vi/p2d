use std::collections::VecDeque;
use crate::solving::pseudo_boolean_datastructure::{Constraint, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;

pub struct Solver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<u32>,
    decision_level: u32,
    learned_clauses: Vec<Constraint>,
    pub propagation_queue: VecDeque<Literal>,
    result_stack: Vec<u128>,
}

impl Solver {
    pub fn new(pseudo_boolean_formula: PseudoBooleanFormula) -> Solver {
        Solver {
            pseudo_boolean_formula,
            assignment_stack: Vec::new(),
            decision_level: 0,
            learned_clauses: Vec::new(),
            propagation_queue: VecDeque::new(),
            result_stack: Vec::new(),
        }
    }

    pub fn solve(&mut self) -> u128 {
        loop {
            self.propagate();

        }
        0
    }

    fn propagate(&mut self) -> bool {
        while !self.propagation_queue.is_empty() {
            let literal = self.propagation_queue.pop_front().unwrap();
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(literal.index as usize).unwrap() {
                let result = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap().propagate(literal.clone());
                match result {
                    Satisfied => {

                    },
                    Unsatisfied => {
                        self.propagation_queue.clear();
                        return false;
                    },
                    ImpliedLiteral(l) => {
                        self.propagation_queue.push_back(l);
                    },
                    LiteralNotInConstraint => {}
                }
            }
        }
        true
    }

    fn decide(&self){

    }
}