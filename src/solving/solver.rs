use std::cmp::PartialEq;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use crate::solving::disconnected_component_datastructure::{Component, ComponentBasedFormula};
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, ConstraintIndex, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::ConstraintIndex::{LearnedClauseIndex, NormalConstraintIndex};
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::solver::AssignmentKind::{FirstDecision, Propagated, SecondDecision};
use crate::solving::solver::AssignmentStackEntry::{Assignment, ComponentBranch};

pub struct Solver {
    pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<AssignmentStackEntry>,
    assignments: Vec<Option<(u32, bool)>>,
    decision_level: u32,
    learned_clauses: Vec<Constraint>,
    learned_clauses_by_variables: Vec<Vec<usize>>,
    result_stack: Vec<u128>,
    number_unsat_constraints: usize,
    number_unassigned_variables: u32,
    cache: HashMap<u64,u128>,
    pub statistics: Statistics,
    variable_in_scope: BTreeSet<usize>,
    constraint_indexes_in_scope: BTreeSet<usize>,
    progress: HashMap<u32, u32>,
    last_progress: f32,
}

impl Solver {
    #[cfg(feature = "disconnected_components")]
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
    #[cfg(feature = "disconnected_components")]
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

        let mut component_based_formula = ComponentBasedFormula::new(self.number_unsat_constraints, self.number_unassigned_variables, self.variable_in_scope.clone(), self.constraint_indexes_in_scope.clone());
        for c in &components {
            let mut component = Component{
                variables: c.clone(),
                number_unassigned_variables: c.len() as u32,
                number_unsat_constraints: 0,
                constraint_indexes_in_scope: BTreeSet::new(),
            };
            for v in c {
                for ci in self.pseudo_boolean_formula.constraints_by_variable.get(*v).unwrap() {
                    component.constraint_indexes_in_scope.insert(*ci);
                }
            }
            let mut constraints = Vec::with_capacity(self.pseudo_boolean_formula.constraints.len() + self.learned_clauses.len());
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

    #[cfg(feature = "disconnected_components")]
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
            learned_clauses_by_variables: Vec::new(),
            learned_clauses: Vec::new(),
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
                learned_clauses: 0,
                propagations_from_learned_clauses: 0,
            },
            assignments: Vec::new(),
            variable_in_scope: BTreeSet::new(),
            progress: HashMap::new(),
            last_progress: -1.0,
            constraint_indexes_in_scope: BTreeSet::new(),
        };
        for i in 0..number_variables{
            solver.assignments.push(None);
            solver.variable_in_scope.insert(i as usize);
            solver.learned_clauses_by_variables.push(Vec::new());
        }
        for c in &solver.pseudo_boolean_formula.constraints {
            if let NormalConstraintIndex(i) = c.index {
                solver.constraint_indexes_in_scope.insert(i);
            }
        }
        solver
    }

    fn get_next_variable(&mut self) -> Option<u32> {
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
        self.statistics.learned_clauses = self.learned_clauses.len();
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
                    if let Some(constraint_index) = self.propagate(var_index, var_sign, FirstDecision) {
                        //at least one constraint violated
                        #[cfg(feature = "clause_learning")]
                        self.safe_conflict_clause(constraint_index);


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


    #[cfg(feature = "clause_learning")]
    fn safe_conflict_clause(&mut self, constraint_index: ConstraintIndex) {
        let constraint = match constraint_index {
            NormalConstraintIndex(i) => {
                self.pseudo_boolean_formula.constraints.get(i).unwrap()
            },
            LearnedClauseIndex(i) => {
                self.learned_clauses.get(i).unwrap()
            }
        };

        let mut variable_index = BTreeMap::new();
        for (index, (sign, kind, decision_level)) in &constraint.assignments {
            //if *decision_level == self.decision_level {
            variable_index.insert(*index, (*kind, *sign, *decision_level));
            //}
        }
        if let Some(learned_constraint) = self.analyze(&mut variable_index) {
            if let LearnedClauseIndex(constraint_index) = learned_constraint.index {
                for (index, _) in &learned_constraint.assignments {
                    self.learned_clauses_by_variables.get_mut(*index).unwrap().push(constraint_index);
                }
                self.learned_clauses.push(learned_constraint);
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
    pub fn propagate(&mut self, variable_index: u32, variable_sign: bool, assignment_kind: AssignmentKind) -> Option<ConstraintIndex> {
        let mut propagation_queue:VecDeque<(u32, bool, AssignmentKind)> = VecDeque::new();
        propagation_queue.push_back((variable_index, variable_sign, assignment_kind));
        while !propagation_queue.is_empty() {

            let (index, sign,kind) = propagation_queue.pop_front().unwrap();
            if !self.variable_in_scope.contains(&(index as usize)){
                //not relevant for this component
                continue;
            }
            if let Some((_,s)) = self.assignments.get(index as usize).unwrap() {
                if s == &sign {
                    //already done exactly this assignment -> skip
                    continue;
                }else{
                    // this is a conflicting assignment
                    panic!("test");
                    //return false;
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
            //propagate from constraints
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(index as usize).unwrap() {
                let result = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap().propagate(Literal{index, positive: sign, factor: 0}, kind, self.decision_level);
                match result {
                    Satisfied => {
                        self.number_unsat_constraints -= 1;
                    },
                    Unsatisfied => {
                        propagation_queue.clear();
                        return Some(NormalConstraintIndex(*constraint_index));
                    },
                    ImpliedLiteral(l) => {
                        propagation_queue.push_back((l.index, l.positive, Propagated(NormalConstraintIndex(*constraint_index))));
                    },
                    NothingToPropagated => {
                    },
                    AlreadySatisfied => {
                    }
                }
            }
            //propagate from learned clauses
            for constraint_index in self.learned_clauses_by_variables.get(index as usize).unwrap() {
                let result = self.learned_clauses.get_mut(*constraint_index).unwrap().propagate(Literal{index, positive: sign, factor: 0}, kind, self.decision_level);
                match result {
                    Satisfied => {
                        //self.number_unsat_constraints -= 1;
                    },
                    Unsatisfied => {
                        //self.statistics.propagations_from_learned_clauses += 1;
                        propagation_queue.clear();
                        return Some(LearnedClauseIndex(*constraint_index));
                    },
                    ImpliedLiteral(l) => {
                        if self.variable_in_scope.contains(&(index as usize)){
                            self.statistics.propagations_from_learned_clauses += 1;
                        }

                        propagation_queue.push_back((l.index, l.positive, Propagated(LearnedClauseIndex(*constraint_index))));
                    },
                    NothingToPropagated => {
                    },
                    AlreadySatisfied => {
                    }
                }
            }

            //TODO also integrate, but maybe check if the assignments should be made somewhere in the assignment stack (e.g. on max decisionlevel of the assigned literals of the constraint that implies)
            for clause in &mut self.learned_clauses {
                let result = clause.simplify();
                let constraint_index = &clause.index;
                match result {
                    Satisfied => {
                        //self.number_unsat_constraints -= 1;
                        //all results here
                    },
                    Unsatisfied => {
                        //self.statistics.propagations_from_learned_clauses += 1;
                        propagation_queue.clear();
                        return Some(*constraint_index);
                    },
                    ImpliedLiteral(l) => {
                        if self.variable_in_scope.contains(&(index as usize)){
                            self.statistics.propagations_from_learned_clauses += 1;
                        }
                        propagation_queue.push_back((l.index, l.positive, Propagated(*constraint_index)));
                    },
                    NothingToPropagated => {
                    },
                    AlreadySatisfied => {
                    }
                }
            }
        }
        None
    }

    #[cfg(feature = "disconnected_components")]
    fn branch_components(&mut self) -> bool {
        let result = self.to_disconnected_components();
        match result {
            Some(component_based_formula) => {
                self.number_unsat_constraints = component_based_formula.components.get(0).unwrap().number_unsat_constraints as usize;
                self.number_unassigned_variables = component_based_formula.components.get(0).unwrap().number_unassigned_variables;
                self.variable_in_scope = component_based_formula.components.get(0).unwrap().variables.clone();
                self.constraint_indexes_in_scope = component_based_formula.components.get(0).unwrap().constraint_indexes_in_scope.clone();
                self.assignment_stack.push(ComponentBranch(component_based_formula));
                true
            },
            None => {
                false
            }
        }
    }

    fn decide(&mut self) -> Option<(u32,bool)>{
        if self.number_unassigned_variables == 0 {
            return None;
        }
        let variable_index = self.get_next_variable();
        match variable_index {
            None => None,
            Some(variable_index) => {
                self.decision_level += 1;
                Some((variable_index, true))
            }
        }
    }

    #[cfg(feature = "show_progress")]
    fn print_progress(&mut self, decision_level: u32) {
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
                        }else if let Propagated(_) = last_assignment.assignment_kind {
                            self.undo_last_assignment();
                        }else if last_assignment.assignment_kind == FirstDecision {
                            let index = last_assignment.variable_index;
                            let sign = last_assignment.variable_sign;

                            #[cfg(feature = "show_progress")]
                            self.print_progress(last_assignment.decision_level);

                            self.undo_last_assignment();
                            let new_sign = !sign;

                            if let Some(constraint_index) = self.propagate(index, new_sign, SecondDecision) {
                                #[cfg(feature = "clause_learning")]
                                self.safe_conflict_clause(constraint_index);

                                self.result_stack.push(0);
                                self.undo_last_assignment();

                            }else{
                                return true;
                            }
                        }else if last_assignment.assignment_kind == SecondDecision {
                            let r1 = self.result_stack.pop().unwrap();
                            let r2 = self.result_stack.pop().unwrap();
                            self.result_stack.push(r1+r2);
                            self.decision_level -= 1;

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
                            self.constraint_indexes_in_scope = last_branch.previous_constraint_indexes_in_scope.clone();
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
                                self.constraint_indexes_in_scope = last_branch.components.get(last_branch.current_component).unwrap().constraint_indexes_in_scope.clone();
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
            //undo in constraints
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(last_assignment.variable_index as usize).unwrap() {
                let constraint = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap();
                if constraint.undo(last_assignment.variable_index, last_assignment.variable_sign) {
                    self.number_unsat_constraints += 1;
                }
            }
            //undo in learned clauses
            for constraint_index in self.learned_clauses_by_variables.get(last_assignment.variable_index as usize).unwrap() {
                let constraint = self.learned_clauses.get_mut(*constraint_index).unwrap();
                constraint.undo(last_assignment.variable_index, last_assignment.variable_sign);
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
                    propagation_set.push((l.index, l.positive, constraint.index));
                }
                _ => {}
            }
        }
        for (index, sign, constraint_index) in propagation_set {
            if !self.propagate(index, sign, Propagated(constraint_index)).is_none(){
                return false;
            }
        }
        true
    }

    #[cfg(feature = "cache")]
    fn cache(&mut self, value: u128) {
        if self.number_unsat_constraints > 0 {
            /*
            if self.cache.contains_key(&calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope, &self.constraint_indexes_in_scope)){

                self.statistics.cache_double_entries += 1;
                let cached_result = self.cache.get(&calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope, &self.constraint_indexes_in_scope)).unwrap();
                let new_result = &value;
                if *cached_result != *new_result as u128 {
                    self.statistics.cache_error += 1;
                }
            }
             */
            self.cache.insert(calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope, &self.constraint_indexes_in_scope), value);
            self.statistics.cache_entries += 1;
        }
    }

    #[cfg(feature = "cache")]
    fn get_cached_result(&mut self) -> Option<u128> {
        match self.cache.get(&calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.variable_in_scope, &self.constraint_indexes_in_scope)) {
            None => None,
            Some(c) => Some(*c)
        }
    }

    #[cfg(feature = "clause_learning")]
    fn analyze(&self, conflicting_variable_indexes: &BTreeMap<usize,(AssignmentKind, bool, u32)>) -> Option<Constraint> {
        let mut reason_set_propagated: Vec<Option<(AssignmentKind, bool, u32)>> = Vec::new();
        let mut reason_set_decision: Vec<Option<(AssignmentKind, bool, u32)>> = Vec::new();
        let mut seen: Vec<bool> = Vec::new();
        for _ in 0..self.pseudo_boolean_formula.number_variables {
            reason_set_propagated.push(None);
            reason_set_decision.push(None);
            seen.push(false);
        }
        let mut counter = 1;
        let mut next_variable_index;
        let mut next_constraint_index;
        let mut number_propagated_reasons = 0;
        let mut decision_node_found = false;

        for (index, (kind, sign, decision_level)) in conflicting_variable_indexes {
            //println!("{} = {} @ {} - {:?}",index,sign,decision_level,kind);
            match kind {
                Propagated(_) => {
                    reason_set_propagated[*index] = Some((*kind, *sign, *decision_level));
                    if self.decision_level == *decision_level {
                        number_propagated_reasons += 1;
                    }
                }
                _ => {
                    if self.decision_level == *decision_level {
                        decision_node_found = true;
                    }
                    reason_set_decision[*index] = Some((*kind, *sign, *decision_level));
                }
            }
        }
        let mut next_assignment_entry = self.assignment_stack.get(self.assignment_stack.len() - counter).unwrap();


        while number_propagated_reasons > 1 || decision_node_found && number_propagated_reasons > 0{
            match next_assignment_entry {
                Assignment(a) => {
                    next_variable_index = a.variable_index as usize;
                    //println!("{} = {} @ {} - {:?}",a.variable_index,a.variable_sign,a.decision_level,a.assignment_kind);
                    if !*seen.get(next_variable_index).unwrap() && !reason_set_propagated.get(a.variable_index as usize).unwrap().is_none() {
                        if let Propagated(constraint_index) = a.assignment_kind {
                            next_constraint_index = constraint_index;

                            if !reason_set_propagated.get(next_variable_index).unwrap().is_none() {
                                number_propagated_reasons -= 1;
                                reason_set_propagated[next_variable_index] = None;
                            }


                            let new_reasons = match next_constraint_index {
                                NormalConstraintIndex(i) => {
                                    self.pseudo_boolean_formula.constraints.get(i).unwrap().calculate_reason(next_variable_index)
                                },
                                LearnedClauseIndex(i) => {
                                    self.learned_clauses.get(i).unwrap().calculate_reason(next_variable_index)
                                }
                            };
                            for (index, (kind, sign, decision_level)) in new_reasons {
                                //println!("{} = {} @ {} - {:?}",index,sign,decision_level,kind);
                                match kind {
                                    Propagated(_) => {
                                        if !seen.get(index).unwrap() {
                                            if self.decision_level == decision_level && reason_set_propagated.get(index).unwrap().is_none(){
                                                number_propagated_reasons += 1;
                                            }
                                            reason_set_propagated[index] = Some((kind, sign, decision_level));
                                        }
                                    }
                                    _ => {
                                        if self.decision_level == decision_level {
                                            decision_node_found = true;
                                        }
                                        reason_set_decision[index] = Some((kind, sign, decision_level));
                                    }
                                }
                            }

                        } else {
                            panic!("Error while learning clause");
                        }
                    }
                    seen[next_variable_index] = true;
                    counter += 1;
                    next_assignment_entry = self.assignment_stack.get(self.assignment_stack.len() - counter).unwrap();

                },
                ComponentBranch(_) => {
                    panic!("Error while learning clause");
                }
            }
        }
        let mut constraint = Constraint{
            assignments: BTreeMap::new(),
            index: LearnedClauseIndex(self.learned_clauses.len()),
            unassigned_literals: BTreeMap::new(),
            literals: Vec::new(),
            sum_true: 0,
            sum_unassigned: 0,
            degree: 1,
            factor_sum: 0,
            hash_value: 0,
            hash_value_old: true,
        };
        for _ in 0..self.pseudo_boolean_formula.number_variables {
            constraint.literals.push(None);
        }
        //println!("decision_level conflict: {}", self.decision_level);
        let mut degree = 1;
        for (index, entry) in reason_set_propagated.iter().enumerate() {
            if let Some((a,sign,decision_level)) = entry {
                constraint.literals[index] = Some(Literal{
                    index: index as u32,
                    positive: !*sign,
                    factor: 1,
                });
                constraint.assignments.insert(index, (*sign,*a,*decision_level));
                constraint.factor_sum += 1;
/*
                if let Propagated(_) = a {
                    if !*sign {
                        print!(" +1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                    }else {
                        print!(" -1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                        degree -= 1;
                    }
                    //print!("[{} = {} @ {}], ",index,sign,decision_level)
                }else{
                    if !*sign {
                        print!(" +1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                    }else {
                        print!(" -1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                        degree -= 1;
                    }
                    //print!("{} = {} @ {}, ",index,sign,decision_level)
                }

 */



            }

        }
        for (index, entry) in reason_set_decision.iter().enumerate() {
            if let Some((a,sign,decision_level)) = entry {
                constraint.literals[index] = Some(Literal{
                    index: index as u32,
                    positive: !*sign,
                    factor: 1,
                });
                constraint.assignments.insert(index, (*sign,*a,*decision_level));
                constraint.factor_sum += 1;
/*
                if let Propagated(_) = a {
                    if !*sign {
                        print!(" +1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                    }else {
                        print!(" -1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                        degree -= 1;
                    }
                    //print!("[{} = {} @ {}], ",index,sign,decision_level)
                }else{
                    if !*sign {
                        print!(" +1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                    }else {
                        print!(" -1 * {}",self.pseudo_boolean_formula.name_map.get_by_right(&(index as u32)).unwrap());
                        degree -= 1;
                    }
                    //print!("{} = {} @ {}, ",index,sign,decision_level)
                }

 */


            }
        }
        //println!(" >= {};", degree);
        Some(constraint)
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
    assignment_kind: AssignmentKind,
}
#[derive(Debug)]
pub struct Statistics {
    cache_hits: u32,
    cache_double_entries: u32,
    cache_error: u32,
    time_to_compute: u128,
    cache_entries: usize,
    learned_clauses: usize,
    propagations_from_learned_clauses: u32,
}

#[derive(PartialEq, Clone, Debug, Eq, Copy)]
pub(crate) enum AssignmentKind {
    Propagated(ConstraintIndex),
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