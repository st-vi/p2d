use std::cmp::PartialEq;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use crate::solving::disconnected_component_datastructure::{Component, ComponentBasedFormula};
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::solver::AssignmentKind::{FirstDecision, Propagated, SecondDecision};
use crate::solving::solver::AssignmentStackEntry::{Assignment, ComponentBranch};

pub struct Solver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<AssignmentStackEntry>,
    assignments: Vec<Option<(u32, bool)>>,
    decision_level: u32,
    _learned_clauses: Vec<Constraint>,
    result_stack: Vec<u128>,
    number_unsat_constraints: usize,
    number_unassigned_variables: u32,
    cache: HashMap<u64,u128>,
    pub statistics: Statistics,
    variable_in_scope: BTreeSet<usize>,
    progress: HashMap<u32, u32>,
    last_progress: f32
}

impl Solver {

    fn create_adjacency_matrix_for_connected_components(&self) -> BTreeMap<usize,BTreeSet<usize>> {
        // create adjacency matrix connection graph
        let mut matrix = BTreeMap::new();
        for (i, constraint_list) in self.pseudo_boolean_formula.constraints_by_variable.iter().enumerate() {
            let mut vector = BTreeSet::new();

            if self.variable_in_scope.contains(&i) && self.assignments.get(i as usize).unwrap().is_none() {
                for constraint_index in constraint_list {
                    let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
                    for variable in &constraint.literals {
                        if let Some(v) = variable {
                            if self.assignments.get(v.index as usize).unwrap().is_none(){
                                vector.insert(v.index as usize);
                            }
                        }
                    }
                }
            }
            if vector.len() > 0 {
                matrix.insert(i, vector);
            }
        }
        matrix
    }
    pub fn to_disconnected_components(&self) -> Option<ComponentBasedFormula> {
        let mut components = Vec::new();
        let matrix = self.create_adjacency_matrix_for_connected_components();
        let mut already_visited: HashSet<usize> = HashSet::new();
        for i in 0..self.pseudo_boolean_formula.number_variables {
            let mut component = BTreeSet::new();

            if self.variable_in_scope.contains(&(i as usize)) && self.assignments.get(i as usize).unwrap().is_none() && self.add_connected_constraints(&matrix, &mut component, i as usize, &mut already_visited) {
                components.push(component);
            }
        }
        if components.len() <= 1 {
            return None;
        }

        let mut component_based_formula = ComponentBasedFormula::new(self.number_unsat_constraints, self.number_unassigned_variables, self.variable_in_scope.clone());
        for c in &components {
            let mut component = Component{
                variables: c.clone(),
                number_unassigned_variables: c.len() as u32,
                number_unsat_constraints: 0,
            };
            let mut constraints = Vec::with_capacity(self.pseudo_boolean_formula.constraints.len());
            constraints.extend((0..self.pseudo_boolean_formula.constraints.len()).map(|_| false));

            for i in c {
                let constraint_indexes = self.pseudo_boolean_formula.constraints_by_variable.get(*i).unwrap();
                for constraint_index in constraint_indexes{
                    constraints[*constraint_index] = true;
                }
            }

            for (i,v) in constraints.iter().enumerate() {
                if *v {
                    if self.pseudo_boolean_formula.constraints.get(i).unwrap().is_unsatisfied() {
                        component.number_unsat_constraints += 1;
                    }
                }
            }

            component_based_formula.components.push(component);
        }

        Some(component_based_formula)
    }

    fn add_connected_constraints(&self, matrix: &BTreeMap<usize,BTreeSet<usize>>, component: &mut BTreeSet<usize>, variable_index: usize, visited: &mut HashSet<usize>) -> bool {
        if visited.contains(&variable_index) {
            return false
        }
        visited.insert(variable_index);
        if let Some(vector) = matrix.get(&variable_index) {
            for index in vector {
                component.insert(*index);
                self.add_connected_constraints(matrix, component, *index, visited);
            }
        }
        true
    }

    pub fn new(pseudo_boolean_formula: PseudoBooleanFormula) -> Solver {
        let number_unsat_constraints = pseudo_boolean_formula.constraints.len();
        let number_variables = pseudo_boolean_formula.number_variables;
        let mut solver = Solver {
            pseudo_boolean_formula,
            assignment_stack: Vec::new(),
            decision_level: 0,
            _learned_clauses: Vec::new(),
            result_stack: Vec::new(),
            number_unsat_constraints,
            number_unassigned_variables: number_variables,
            cache: HashMap::with_capacity(100),
            statistics: Statistics {
                cache_hits: 0,
                cache_double_entries: 0,
                cache_error: 0,
                time_to_compute: 0,
                cache_entries: 0,
            },
            assignments: Vec::new(),
            variable_in_scope: BTreeSet::new(),
            progress: HashMap::new(),
            last_progress: -1.0,
        };
        for i in 0..number_variables{
            solver.assignments.push(None);
            solver.variable_in_scope.insert(i as usize);
        }
        solver
    }

    fn get_next_variable(&self) -> Option<u32> {
        //TODO better heuristic?
/*
        let mut min_number_unsat_constraint = self.number_unsat_constraints;
        let mut index = None;

        for (i, a) in self.assignments.iter().enumerate() {
            if a.is_none() {
                let tmp_dis = self.to_disconnected_components();
                if let Some(d) = tmp_dis {
                    let m = d.components.iter().map(|x| x.number_unsat_constraints).max().unwrap();
                    if m < min_number_unsat_constraint as u32 {
                        min_number_unsat_constraint = m as usize;
                        index = Some(i as u32);
                    }
                }
            }
        }

        if index.is_none() {
            for constraint in &self.pseudo_boolean_formula.constraints {
                if constraint.is_unsatisfied(){
                    for literal in &constraint.unassigned_literals {
                        if let Some(l) = literal {
                            if *self.variable_in_scope.get(l.index as usize).unwrap() {
                                return Some(l.index);
                            }
                        }
                    }
                }
            }
            None
        }else{
            index
        }

 */



/*

        for constraint in &self.pseudo_boolean_formula.constraints {
            if constraint.is_unsatisfied(){
                for (_,literal) in &constraint.unassigned_literals {
                    if *self.variable_in_scope.get(literal.index as usize).unwrap() {
                        return Some(literal.index);
                    }
                }
            }
        }
        None



 */





        let mut counter: Vec<u64> = Vec::new();
        for _ in 0..self.pseudo_boolean_formula.number_variables {
            counter.push(0);
        }


        for constraint in &self.pseudo_boolean_formula.constraints {
            if constraint.is_unsatisfied(){
                for (_,literal) in &constraint.unassigned_literals {
                    if self.variable_in_scope.contains(&(literal.index as usize)) {
                        let tmp_res = counter.get(literal.index as usize).unwrap();
                        counter[literal.index as usize] = tmp_res + 1;
                    }
                }
            }
        }

        let mut max_index: usize = 0;
        let mut max_value: u64 = 0;
        for (k,v) in counter.iter().enumerate() {
            if v > &max_value {
                max_value = *v;
                max_index = k;
            }
        }
        Some(max_index as u32)


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
            //after simplifying formula violated constraint detected
            return 0;
        }
        loop {
            if self.number_unsat_constraints <= 0 {
                //current assignment satisfies all constraints
                self.result_stack.push(2_u128.pow(self.number_unassigned_variables));
                if !self.backtrack(){
                    //nothing to backtrack to, we searched the whole space
                    return self.result_stack.pop().unwrap();
                }
                continue
            }

            #[cfg(feature = "cache")]
            {
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
            }

            #[cfg(feature = "disconnected_components")]
            {
                if self.decision_level < 8 || self.decision_level % 4 == 1 {
                    if let Some(assignment_entry) = self.assignment_stack.last() {
                        match assignment_entry {
                            ComponentBranch(_) => {},
                            Assignment(_) => {
                                if self.branch_components() {
                                    continue;
                                }
                            }
                        }
                    }else{
                        if self.branch_components() {
                            continue;
                        }
                    }
                }
            }

            let decided_literal = self.decide();
            match decided_literal {
                None => {
                    //there are no free variables to assign a value to
                    self.result_stack.push(0);
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return self.result_stack.pop().unwrap();
                    }
                },
                Some((var_index, var_sign)) => {
                    //set and propagate the new decided variable
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

    /// This function is used to set a variable to true or false in all constraints.
    /// It also detects implied variables and also sets them until no more implications are left.
    /// It adapts all constraints, the assignment_stack and the number of unsatisfied constraints
    /// accordingly. This means all relevant datastructures for setting a variable assignment
    /// are handled by this function.
    /// # Arguments
    /// * `variable_index` - The index of the variable to be set to true or false
    /// * `variable_sign` - true or false depending on what the variable is set to
    /// * `assignment_kind` - depending on how the decision for this assigment was made
    /// # Returns
    /// true: the variable assignment and all implications are set and no constraints were violated
    /// false: the assignment resulted in conflicting implications
    pub fn propagate(&mut self, variable_index: u32, variable_sign: bool, assignment_kind: AssignmentKind) -> bool {
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
            self.number_unassigned_variables -= 1;
            self.assignment_stack.push(Assignment(VariableAssignment {
                assignment_kind: kind,
                decision_level: self.decision_level,
                variable_index: index,
                variable_sign: sign,
            }));
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

    fn branch_components(&mut self) -> bool {
        let result = self.to_disconnected_components();
        match result {
            Some(component_based_formula) => {
                self.number_unsat_constraints = component_based_formula.components.get(0).unwrap().number_unsat_constraints as usize;
                self.number_unassigned_variables = component_based_formula.components.get(0).unwrap().number_unassigned_variables;
                self.variable_in_scope = component_based_formula.components.get(0).unwrap().variables.clone();
                self.assignment_stack.push(ComponentBranch(component_based_formula));
                true
            },
            None => {
                false
            }
        }
    }

    fn decide(&mut self) -> Option<(u32,bool)>{
        self.decision_level += 1;
        if self.number_unassigned_variables == 0 {
            return None;
        }
        let variable_index = self.get_next_variable();
        match variable_index {
            None => None,
            Some(variable_index) => {
                Some((variable_index, true))
            }
        }
    }

    /// This functions backtracks manually by chancing the necessary data structures.
    /// Backtracking means: undoing all assignments until the last decision. If the decision was a first
    /// decision, change the sign of the variable, if not also undo it and backtrack further.
    /// The function also collects the results and caches them.
    /// # Returns
    /// true: the function successfully backtracked to a not violated and not yet visited state
    /// false: during backtracking the function got back to the first decision and discovered, that
    /// the whole search space has been searched
    fn backtrack(&mut self) -> bool {
        loop {
            if let Some(top_element) = self.assignment_stack.last() {
                match top_element {
                    Assignment(last_assignment) => {
                        if last_assignment.decision_level == 0{
                            return false;
                        }else if last_assignment.assignment_kind == Propagated {
                            self.undo_last_assignment();
                        }else if last_assignment.assignment_kind == FirstDecision {
                            let index = last_assignment.variable_index;
                            let sign = last_assignment.variable_sign;
                            let decision_level = last_assignment.decision_level;

                            #[cfg(feature = "show_progress")]
                            {
                                if decision_level < 9 {
                                    let res = self.progress.get(&decision_level);
                                    match res {
                                        None => {
                                            self.progress.insert(decision_level, 1);
                                        },
                                        Some(v) => {
                                            self.progress.insert(decision_level, *v + 1);
                                        }
                                    }
                                    for i in decision_level + 1..9{
                                        self.progress.remove(&i);
                                    }
                                }
                                let mut progress = 0.0;
                                for (k,v) in &self.progress {
                                    progress += (100.0 / 2_i32.pow(*k) as f32) * (*v as f32);
                                }
                                if progress != self.last_progress {
                                    self.last_progress = progress;
                                    println!("{progress} %");
                                }
                            }

                            self.undo_last_assignment();
                            let new_sign = !sign;
                            self.decision_level = decision_level;
                            if self.propagate(index, new_sign, SecondDecision) {
                                return true;
                            }else{
                                self.result_stack.push(0);
                                self.undo_last_assignment();
                            }
                        }else if last_assignment.assignment_kind == SecondDecision {
                            let r1 = self.result_stack.pop().unwrap();
                            let r2 = self.result_stack.pop().unwrap();
                            self.result_stack.push(r1+r2);

                            self.undo_last_assignment();
                            self.cache(r1+r2);
                        }
                    },
                    ComponentBranch(last_branch) => {
                        //undo branch
                        if last_branch.current_component == last_branch.components.len() -1 {
                            // we processed all components
                            let mut branch_result = 1;
                            for _ in 0..last_branch.components.len(){
                                branch_result = branch_result * self.result_stack.pop().unwrap();
                            }

                            self.result_stack.push(branch_result);

                            self.number_unassigned_variables = last_branch.previous_number_unassigned_variables as u32;
                            self.number_unsat_constraints = last_branch.previous_number_unsat_constraints;
                            self.variable_in_scope = last_branch.previous_variables_in_scope.clone();
                            self.assignment_stack.pop();

                        }else{
                            // process next component

                            if let ComponentBranch(mut last_branch) = self.assignment_stack.pop().unwrap() {
                                //TODO if one component result is zero backtrack beyond branch: It does not work like this
/*
                                if *self.result_stack.last().unwrap() == 0 {
                                    for _ in 0..=last_branch.current_component {
                                        self.result_stack.pop();
                                    }
                                    self.result_stack.push(0);
                                    self.number_unassigned_variables = last_branch.previous_number_unassigned_variables as u32;
                                    self.number_unsat_constraints = last_branch.previous_number_unsat_constraints;
                                    self.variable_in_scope = last_branch.previous_variables_in_scope.clone();
                                    self.assignment_stack.pop();
                                    continue;
                                }

 */


                                last_branch.current_component += 1;
                                self.number_unassigned_variables = last_branch.components.get(last_branch.current_component).unwrap().number_unassigned_variables;
                                self.number_unsat_constraints = last_branch.components.get(last_branch.current_component).unwrap().number_unsat_constraints as usize;
                                self.variable_in_scope = last_branch.components.get(last_branch.current_component).unwrap().variables.clone();
                                self.assignment_stack.push(ComponentBranch(last_branch));
                            }
                            return true;

                        }
                    }
                }

            }else {
                return false;
            }

        }
    }

    /// Undos the last assignment. Just one assignment independent of the decision kind.
    fn undo_last_assignment(&mut self) {
        if let Assignment(last_assignment) = self.assignment_stack.pop().unwrap(){
            self.assignments[last_assignment.variable_index as usize] = None;
            self.number_unassigned_variables += 1;
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(last_assignment.variable_index as usize).unwrap() {
                let constraint = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap();
                if constraint.undo(last_assignment.variable_index, last_assignment.variable_sign) {
                    self.number_unsat_constraints += 1;
                }
            }
        }
    }

    /// Checks if there are any implications and if so propagates them until there are no more implications
    /// # Returns
    /// true: all implications were assigned without any conflicts
    /// false: a conflict occurred and the formula is therefore unsatisfiable
    fn simplify(&mut self) -> bool {
        let mut propagation_set = Vec::new();
        for constraint in &mut self.pseudo_boolean_formula.constraints {
            match constraint.simplify(){
                Satisfied => {
                    self.number_unsat_constraints -= 1;
                },
                Unsatisfied => {
                    return false;
                },
                ImpliedLiteral(l) => {
                    propagation_set.push((l.index, l.positive));
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

    fn cache(&mut self, value: u128) {
        if self.number_unsat_constraints > 0 {
            if self.cache.contains_key(&calculate_hash(&self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope)){
                self.statistics.cache_double_entries += 1;
                let cached_result = self.cache.get(&calculate_hash(&self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope)).unwrap();
                let new_result = &value;
                if *cached_result != *new_result as u128 {
                    self.statistics.cache_error += 1;
                }
            }
            self.cache.insert(calculate_hash(&self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope), value);
            self.statistics.cache_entries += 1;
        }
    }

    fn get_cached_result(&self) -> Option<u128> {
        match self.cache.get(&calculate_hash(&self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope)) {
            None => None,
            Some(c) => Some(*c)
        }
    }
}

#[derive(Clone)]
enum AssignmentStackEntry {
    Assignment(VariableAssignment),
    ComponentBranch(ComponentBasedFormula)
}
#[derive(Clone)]
struct VariableAssignment {
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

#[derive(PartialEq, Clone)]
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
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, 4080389785);
    }

    #[test]
    fn test_ex_4() {
        let opb_file = parsing::parser::parse("a + b + c >= 1;\nx + y + z >= 2;\na + x >= 1;\nx1 + x2 + x3 >= 1;\n").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, 175);
    }

    #[test]
    fn test_ex_5() {
        let file_content = fs::read_to_string("./test_models/financialservices01.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, 97451212554676);
    }
}