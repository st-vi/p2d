use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{DefaultHasher, Hash, Hasher};
use pest::pratt_parser::Op;
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::recursive_solving::AssignmentKind::{FirstDecision, Propagated, SecondDecision};

pub struct RecSolver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<Assignment>,
    assignments: Vec<Option<(u32, bool)>>,
    decision_level: u32,
    learned_clauses: Vec<Constraint>,
    result_stack: Vec<u128>,
    number_unsat_constraints: usize,
    //TODO number of unassigned variables should be enough
    unassigned_variables: HashSet<u32>,
    model_counter: u128,
    cache: HashMap<u64,u128>,
    pub statistics: Statistics,
}

impl RecSolver {
    pub fn new(pseudo_boolean_formula: PseudoBooleanFormula) -> RecSolver {
        let number_unsat_constraints = pseudo_boolean_formula.constraints.len();
        let mut unassigned_variables = HashSet::new();
        let number_variables = pseudo_boolean_formula.number_variables;
        for i in 0..number_variables{
            unassigned_variables.insert(i);
        }
        let mut solver = RecSolver {
            pseudo_boolean_formula,
            assignment_stack: Vec::new(),
            decision_level: 0,
            learned_clauses: Vec::new(),
            result_stack: Vec::new(),
            number_unsat_constraints,
            unassigned_variables,
            model_counter: 0,
            cache: HashMap::new(),
            statistics: Statistics {
                cache_hits: 0,
                cache_double_entries: 0,
                cache_error: 0,
                time_to_compute: 0,
                cache_entries: 0,
            },
            assignments: Vec::new(),
        };
        for i in 0..number_variables{
            solver.assignments.push(None);
        }
        solver
    }

    fn get_next_variable(&self) -> Option<u32> {
        for constraint in &self.pseudo_boolean_formula.constraints {
            if constraint.is_unsatisfied(){
                for literal in &constraint.unassigned_literals {
                    if let Some(l) = literal {
                        return Some(l.index);
                    }
                }
            }
        }
        None
    }

    fn count(&mut self, start_progress: u32, end_progress: u32) -> u128 {
        let cache_entry = self.get_cached_result();
        match cache_entry {
            Some(c) => {
                self.statistics.cache_hits += 1;
                c
            },
            None => {
                self.decision_level += 1;
                if self.number_unsat_constraints <= 0{
                    return 2_u128.pow(self.unassigned_variables.len() as u32)
                }
                if self.unassigned_variables.len() == 0 {
                    return 0;
                }
                let mid_progress = start_progress + (end_progress - start_progress) / 2;

                let variable_index = self.get_next_variable();
                match variable_index {
                    None => {return 0;}
                    Some(variable_index) => {
                        let mut c1 = 0;
                        if self.propagate(variable_index, true, FirstDecision) {
                            c1 = self.count(start_progress,mid_progress);
                        }
                        if(end_progress - start_progress >= 1){
                            println!("{mid_progress} %");
                        }
                        self.undo_until_last_decision();
                        let mut c2 = 0;
                        if self.propagate(variable_index, false,SecondDecision) {
                            c2 = self.count(mid_progress, end_progress);
                        }

                        self.undo_until_last_decision();
                        self.decision_level -= 1;
                        self.cache(c1 + c2);
                        c1 + c2
                    }
                }

            }
        }
    }

    fn undo_until_last_decision(&mut self) -> bool{
        loop {
            if let Some(top_element) = self.assignment_stack.last(){
                if top_element.decision_level == 0{
                    return false;
                }else if top_element.assignment_kind == Propagated {
                    self.undo_last_assignment();
                }else if top_element.assignment_kind == FirstDecision || top_element.assignment_kind == SecondDecision {
                    self.undo_last_assignment();
                    return true;
                }else {
                    return false;
                }
            }
        }
    }

    pub fn solve(&mut self) -> u128 {
        use std::time::Instant;
        let now = Instant::now();
        if !self.simplify(){
            return 0;
        }
        let res = self.count(0, 100);
        let elapsed = now.elapsed();
        self.statistics.time_to_compute = elapsed.as_millis();
        res
    }

    fn propagate(&mut self, variable_index: u32, variable_sign: bool, assignment_kind: AssignmentKind) -> bool {
        let mut propagation_queue:VecDeque<(u32, bool, AssignmentKind)> = VecDeque::new();
        propagation_queue.push_back((variable_index, variable_sign, assignment_kind));
        while !propagation_queue.is_empty() {
            let (index, sign,kind) = propagation_queue.pop_front().unwrap();
            if let Some((a,s)) = self.assignments.get(index as usize).unwrap() {
                if s == &sign {
                    //already done exactly this assignment -> skip
                    continue;
                }else{
                    // this is a conflicting assignment
                    return false;
                }
            }
            self.unassigned_variables.remove(&index);
            self.assignment_stack.push(Assignment{
                assignment_kind: kind,
                decision_level: self.decision_level,
                variable_index: index,
                variable_sign: sign,
            });
            self.assignments[index as usize] = Some((index, sign));
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
                        propagation_queue.push_back((l.index, l.positive, Propagated));
                    },
                    NothingToPropagated => {},
                    AlreadySatisfied => {}
                }
            }
        }
        true
    }





    fn undo_last_assignment(&mut self) {
        let last_assignment = self.assignment_stack.pop().unwrap();
        self.assignments[last_assignment.variable_index as usize] = None;
        self.unassigned_variables.insert(last_assignment.variable_index);
        for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(last_assignment.variable_index as usize).unwrap() {
            let constraint = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap();
            if constraint.undo(last_assignment.variable_index, last_assignment.variable_sign) {
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
                    propagation_set.insert((l.index, l.positive));
                }
                _ => {}
            }
        }
        for (index, sign) in propagation_set {
            if !self.propagate(index, sign, Propagated){
                return false;
            }
        }
        true
    }

    fn hash_state(&self) -> u64 {
        let mut s = DefaultHasher::new();
        let mut is_true = true;

        for c in &self.pseudo_boolean_formula.constraints {
            if c.is_unsatisfied() {
                c.hash(&mut s);
                is_true = false;
            }else{
                false.hash(&mut s);
            }
        }
        if is_true {
            println!("is true");
        }

        s.finish()
    }

    fn cache(&mut self, value: u128) {
        if self.number_unsat_constraints > 0 {
            if self.cache.contains_key(&calculate_hash(&self.pseudo_boolean_formula, self.unassigned_variables.len() as u32)){
                self.statistics.cache_double_entries += 1;
                let cached_result = self.cache.get(&calculate_hash(&self.pseudo_boolean_formula, self.unassigned_variables.len() as u32)).unwrap();
                let new_result = &value;

                if cached_result != new_result {
                    let state = self.hash_state();
                    self.statistics.cache_error += 1;
                    println!("old: {} - new: {} - hash_value: {}", cached_result, new_result, state);
                }
            }
            self.cache.insert(calculate_hash(&self.pseudo_boolean_formula, self.unassigned_variables.len() as u32), value);
            self.statistics.cache_entries += 1;
        }
    }

    fn get_cached_result(&self) -> Option<u128> {
        match self.cache.get(&calculate_hash(&self.pseudo_boolean_formula, self.unassigned_variables.len() as u32)) {
            None => None,
            Some(c) => Some(*c)
        }
    }
}

struct Assignment {
    decision_level: u32,
    variable_index: u32,
    variable_sign: bool,
    assignment_kind: AssignmentKind
}
#[derive(Debug)]
pub struct Statistics {
    cache_hits: u32,
    cache_double_entries: u32,
    cache_error: u32,
    time_to_compute: u128,
    cache_entries: u64
}

#[derive(PartialEq)]
enum AssignmentKind {
    Propagated,
    FirstDecision,
    SecondDecision
}

#[cfg(test)]
mod tests {
    use std::fs;
    use crate::parsing;
    use super::*;

    #[test]
    fn test_ex_1() {
        let opb_file = parsing::parser::parse("x1 + x2 >= 0;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = RecSolver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 18);
    }

    #[test]
    fn test_ex_2() {
        let opb_file = parsing::parser::parse("x1 + x2 >= 1;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = RecSolver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 17);
    }

    #[test]
    fn test_ex_3() {
        let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = RecSolver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 4080389785);
    }
}