use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{DefaultHasher, Hash, Hasher};
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::solver::AssignmentKind::{FirstDecision, Propagated, SecondDecision};

pub struct Solver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<Assignment>,
    assignments: Vec<Option<(u32, bool)>>,
    decision_level: u32,
    _learned_clauses: Vec<Constraint>,
    result_stack: Vec<u128>,
    number_unsat_constraints: usize,
    //TODO number of unassigned variables should be enough
    unassigned_variables: HashSet<u32>,
    model_counter: u128,
    cache: HashMap<u64,u128>,
    pub statistics: Statistics,
}

impl Solver {
    pub fn new(pseudo_boolean_formula: PseudoBooleanFormula) -> Solver {
        let number_unsat_constraints = pseudo_boolean_formula.constraints.len();
        let mut unassigned_variables = HashSet::new();
        let number_variables = pseudo_boolean_formula.number_variables;
        for i in 0..number_variables{
            unassigned_variables.insert(i);
        }
        let mut solver = Solver {
            pseudo_boolean_formula,
            assignment_stack: Vec::new(),
            decision_level: 0,
            _learned_clauses: Vec::new(),
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
        for _ in 0..number_variables{
            solver.assignments.push(None);
        }
        solver
    }

    fn get_next_variable(&self) -> Option<u32> {
        //TODO better heuristic?
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

    pub fn solve(&mut self) -> u128 {
        use std::time::Instant;
        let now = Instant::now();
        let result = self.count();
        let elapsed = now.elapsed();
        self.statistics.time_to_compute = elapsed.as_millis();
        result
    }

    fn count(&mut self) -> u128 {
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

            //cache start
            let cached_result = self.get_cached_result();
            if let Some(c) = cached_result {
                    self.result_stack.push(c);
                    self.statistics.cache_hits += 1;
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return self.result_stack.pop().unwrap();
                    }
                    continue;
            }
            //cache end

            let decided_literal = self.decide();
            match decided_literal {
                None => {
                    self.result_stack.push(0);
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return self.result_stack.pop().unwrap();
                    }
                },
                Some((var_index, var_sign)) => {
                    if !self.propagate(var_index, var_sign, FirstDecision){
                        //at least one constraint violated
                        self.result_stack.push(0);
                        if !self.backtrack(){
                            //nothing to backtrack to, we searched the whole space
                            return self.result_stack.pop().unwrap();
                        }
                    }
                }
            }
        }
    }

    fn propagate(&mut self, variable_index: u32, variable_sign: bool, assignment_kind: AssignmentKind) -> bool {
        let mut propagation_queue:VecDeque<(u32, bool, AssignmentKind)> = VecDeque::new();
        propagation_queue.push_back((variable_index, variable_sign, assignment_kind));
        while !propagation_queue.is_empty() {
            let (index, sign,kind) = propagation_queue.pop_front().unwrap();
            if let Some((_,s)) = self.assignments.get(index as usize).unwrap() {
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

    fn decide(&mut self) -> Option<(u32,bool)>{
        self.decision_level += 1;
        if self.unassigned_variables.len() == 0 {
            return None;
        }
        let variable_index = self.get_next_variable();
        match variable_index {
            None => None,
            Some(variable_index) => Some((variable_index, true))
        }
    }

    fn backtrack(&mut self) -> bool {
        loop {
            if let Some(top_element) = self.assignment_stack.last(){
                if top_element.decision_level == 0{
                    return false;
                }else if top_element.assignment_kind == Propagated {
                    self.undo_last_assignment();
                }else if top_element.assignment_kind == FirstDecision {
                    let index = top_element.variable_index;
                    let sign = top_element.variable_sign;
                    let decision_level = top_element.decision_level;
                    //self.cache();
                    self.undo_last_assignment();
                    let new_sign = !sign;
                    self.decision_level = decision_level;
                    self.propagate(index, new_sign, SecondDecision);

                    /*
                    if self.number_unsat_constraints > 0 {
                        let cached_result = self.get_cached_result();
                        match cached_result {
                            Some(c) => {
                                self.result_stack.push(c);
                                self.statistics.cache_hits += 1;
                                continue;
                            },
                            None => {

                                return true
                            }
                        }
                    }else{
                        return true;
                    }

                     */
                    return true;
                }else if top_element.assignment_kind == SecondDecision {
                    let r1 = self.result_stack.pop().unwrap();
                    let r2 = self.result_stack.pop().unwrap();
                    self.result_stack.push(r1+r2);

                    self.undo_last_assignment();
                    self.cache(r1+r2);
                }
            }else {
                return false;
            }

        }
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

                if *cached_result != *new_result as u128 {
                    let state = self.hash_state();
                    self.statistics.cache_error += 1;
                    println!("old: {} - new: {} - hash_value: {}", cached_result, new_result, state);
                }
            }
            self.cache.insert(calculate_hash(&self.pseudo_boolean_formula.clone(), self.unassigned_variables.len() as u32), value);
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
    cache_entries: usize,
}

#[derive(PartialEq)]
pub(crate) enum AssignmentKind {
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

    #[test]
    fn test_ex_3() {
        let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, 4080389785);
    }
}