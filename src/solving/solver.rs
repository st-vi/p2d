use std::cmp::PartialEq;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use crate::partitioning::disconnected_component_datastructure::{Component, ComponentBasedFormula};
use crate::partitioning::hypergraph_partitioning::partition;
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, ConstraintIndex, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::ConstraintIndex::{LearnedClauseIndex, NormalConstraintIndex};
use crate::solving::pseudo_boolean_datastructure::ConstraintType::GreaterEqual;
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
    result_stack: Vec<BigUint>,
    number_unsat_constraints: usize,
    number_unassigned_variables: u32,
    cache: HashMap<u64,BigUint>,
    pub statistics: Statistics,
    variable_in_scope: BTreeSet<usize>,
    constraint_indexes_in_scope: BTreeSet<usize>,
    progress: HashMap<u32, f32>,
    last_progress: f32,
    next_variables: Vec<u32>,
    progress_split: u128,
}

impl Solver {
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
            next_variables: Vec::new(),
            progress_split: 1
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

    pub fn solve(&mut self) -> BigUint {
        use std::time::Instant;
        let now = Instant::now();
        let result = self.count();
        #[cfg(feature = "show_progress")]
        self.print_progress(0);
        let elapsed = now.elapsed();
        self.statistics.time_to_compute = elapsed.as_millis();
        self.statistics.learned_clauses = self.learned_clauses.len();
        result
    }

    fn count(&mut self) -> BigUint {
        if !self.simplify(){
            //after simplifying formula violated constraint detected
            return BigUint::zero();
        }

        loop {
            if self.number_unsat_constraints <= 0 {
                //current assignment satisfies all constraints
                self.result_stack.push(BigUint::from(2 as u32).pow(self.number_unassigned_variables));
                self.next_variables.clear();
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
                    self.next_variables.clear();
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


                if self.branch_components() {
                    continue;
                }

/*
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

 */
            }

            let decided_literal = self.decide();
            match decided_literal {
                None => {
                    //there are no free variables to assign a value to
                    self.result_stack.push(BigUint::zero());
                    self.next_variables.clear();
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

                        self.result_stack.push(BigUint::zero());
                        self.next_variables.clear();
                        if !self.backtrack(){
                            //nothing to backtrack to, we searched the whole space
                            return self.result_stack.pop().unwrap();
                        }
                    }
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
                    propagation_set.push((l.index, l.positive, constraint.index));
                },
                ImpliedLiteralList(list) => {
                    for l in list {
                        propagation_set.push((l.index, l.positive, constraint.index));
                    }
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
        let mut propagation_queue:VecDeque<(u32, bool, AssignmentKind, bool)> = VecDeque::new();
        propagation_queue.push_back((variable_index, variable_sign, assignment_kind, false));

        //TODO check if the assignments should be made somewhere in the assignment stack (e.g. on max decisionlevel of the assigned literals of the constraint that implies)

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
                    propagation_queue.push_back((l.index, l.positive, Propagated(*constraint_index), true));
                },
                NothingToPropagated => {
                },
                AlreadySatisfied => {
                },
                ImpliedLiteralList(list) => {
                    for l in list {
                        propagation_queue.push_back((l.index, l.positive, Propagated(*constraint_index), true));
                    }
                }
            }
        }






        while !propagation_queue.is_empty() {

            let (index, sign,kind, from_learned_clause) = propagation_queue.pop_front().unwrap();
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
            if from_learned_clause {
                self.statistics.propagations_from_learned_clauses += 1;
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
                        propagation_queue.push_back((l.index, l.positive, Propagated(NormalConstraintIndex(*constraint_index)),false));
                    },
                    NothingToPropagated => {
                    },
                    AlreadySatisfied => {
                    },
                    ImpliedLiteralList(list) => {
                        for l in list {
                            propagation_queue.push_back((l.index, l.positive, Propagated(NormalConstraintIndex(*constraint_index)), false));
                        }
                    }
                }
            }
            //propagate from learned clauses
            for constraint_index in self.learned_clauses_by_variables.get(index as usize).unwrap() {
                let result = self.learned_clauses.get_mut(*constraint_index).unwrap().propagate(Literal{index, positive: sign, factor: 0}, kind, self.decision_level);
                match result {
                    Satisfied => {},
                    Unsatisfied => {
                        //self.statistics.propagations_from_learned_clauses += 1;
                        propagation_queue.clear();
                        return Some(LearnedClauseIndex(*constraint_index));
                    },
                    ImpliedLiteral(l) => {
                        propagation_queue.push_back((l.index, l.positive, Propagated(LearnedClauseIndex(*constraint_index)),true));
                    },
                    NothingToPropagated => {
                    },
                    AlreadySatisfied => {
                    },
                    ImpliedLiteralList(list) => {
                        for l in list {
                            propagation_queue.push_back((l.index, l.positive, Propagated(LearnedClauseIndex(*constraint_index)), true));
                        }
                    }
                }
            }
        }
        None
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
                                self.result_stack.push(BigUint::zero());

                            }else{
                                return true;
                            }
                        }else if last_assignment.assignment_kind == SecondDecision {
                            let r1 = self.result_stack.pop().unwrap();
                            let r2 = self.result_stack.pop().unwrap();
                            let res = r1+r2;
                            self.result_stack.push(res.clone());
                            self.next_variables.clear();
                            self.decision_level -= 1;

                            self.undo_last_assignment();

                            #[cfg(feature = "cache")]
                            self.cache(res);
                        }
                    },
                    ComponentBranch(last_branch) => {
                        //undo branch
                        if last_branch.current_component == last_branch.components.len() -1 {
                            // we processed all components
                            #[cfg(feature = "show_progress")]
                            if self.decision_level < 5{
                                self.progress_split /= last_branch.components.len() as u128;
                            }

                            let mut branch_result = BigUint::one();
                            for _ in 0..last_branch.components.len(){
                                branch_result = branch_result * self.result_stack.pop().unwrap();
                            }

                            self.result_stack.push(branch_result);
                            self.next_variables.clear();

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

    fn get_next_variable(&mut self) -> Option<u32> {

        self.next_variables = self.next_variables.iter().filter(|x| self.assignments.get(**x as usize).unwrap().is_none() && self.variable_in_scope.contains(&(**x as usize))).map(|x| *x).collect();
        let mut counter: Vec<u32> = Vec::new();
        for _ in 0..self.pseudo_boolean_formula.number_variables {
            counter.push(0);
        }

        if self.next_variables.len() == 1 {
            return self.next_variables.pop();
        }
        if self.next_variables.len() > 0 {
            for variable_index in &self.next_variables {
                for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(*variable_index as usize).unwrap() {
                    let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
                    if constraint.is_unsatisfied(){
                        for (_,literal) in &constraint.unassigned_literals {
                            let tmp_res = counter.get(literal.index as usize).unwrap();
                            counter[literal.index as usize] = tmp_res + 1;

                        }
                    }
                }
            }
            let mut max_index: Option<u32> = None;
            let mut max_value: Option<u32> = None;
            for (k,v) in counter.iter().enumerate() {
                if *v > 0 && max_value.is_none() {
                    max_value = Some(*v);
                    max_index = Some(k as u32);
                } else if let Some(value) = max_value {
                    if v > &value {
                        max_value = Some(*v);
                        max_index = Some(k as u32);
                    }
                }

            }
            if let Some(_) = max_index {
                return max_index;
            }else {
                self.next_variables.clear();
            }

        }






        /*
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

         */

        for constraint_index in &self.constraint_indexes_in_scope {
            let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
            if constraint.is_unsatisfied() {
                for (_,literal) in &constraint.unassigned_literals {
                    let tmp_res = counter.get(literal.index as usize).unwrap();
                    counter[literal.index as usize] = tmp_res + 1;

                }
            }
        }
        /*
                for variable_index in &self.variable_in_scope {
                    for constraint_index in self.learned_clauses_by_variables.get(*variable_index).unwrap() {
                        let constraint = self.learned_clauses.get(*constraint_index).unwrap();
                        if constraint.is_unsatisfied(){
                            for (_,literal) in &constraint.unassigned_literals {
                                let tmp_res = counter.get(literal.index as usize).unwrap();
                                counter[literal.index as usize] = tmp_res + 1;

                            }
                        }
                    }
                }

         */







        let mut max_index: usize = 0;
        let mut max_value: u32 = 0;
        for (k,v) in counter.iter().enumerate() {
            if v > &max_value {
                max_value = *v;
                max_index = k;
            }
        }
        Some(max_index as u32)
    }

    #[cfg(feature = "cache")]
    fn cache(&mut self, value: BigUint) {
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
            self.cache.insert(calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.constraint_indexes_in_scope), value);
            self.statistics.cache_entries += 1;
        }
    }

    #[cfg(feature = "cache")]
    fn get_cached_result(&mut self) -> Option<BigUint> {
        match self.cache.get(&calculate_hash(&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.constraint_indexes_in_scope)) {
            None => None,
            Some(c) => Some(c.clone())
        }
    }

    #[cfg(feature = "disconnected_components")]
    fn branch_components(&mut self) -> bool {
        let result = self.to_disconnected_components();
        match result {
            Some(component_based_formula) => {
                #[cfg(feature = "show_progress")]
                if self.decision_level < 5{
                    self.progress_split *= component_based_formula.components.len() as u128;
                }
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

    #[cfg(feature = "disconnected_components")]
    pub fn to_disconnected_components(&mut self) -> Option<ComponentBasedFormula> {
        //let mut components = Vec::new();
        let mut pins = Vec::new();
        let mut x_pins = Vec::new();
        //hg index to FM index
        let mut variable_index_map = Vec::new();
        let mut variable_index_map_reverse = BTreeMap::new();
        let mut current_variable_index = 0;
        //hg index to FM index
        let mut constraint_index_map = Vec::new();
        let mut constraint_index_map_reverse: BTreeMap<usize, u32> = BTreeMap::new();
        let mut current_constraint_index = 0;
        let mut single_variables = BTreeSet::new();
        x_pins.push(0);

        for variable_in_scope in &self.variable_in_scope {
            if self.assignments.get(*variable_in_scope).unwrap().is_none() {
                let mut tmp_constraint_indexes = Vec::new();
                for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(*variable_in_scope).unwrap() {
                    let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
                    if constraint.is_unsatisfied() {
                        if let NormalConstraintIndex(index) = constraint.index {
                            tmp_constraint_indexes.push(index);
                        }

                    }
                }
                if tmp_constraint_indexes.len() > 0 {
                    variable_index_map.push(variable_in_scope);
                    variable_index_map_reverse.insert(variable_in_scope, current_variable_index);
                    current_variable_index += 1;
                    for constraint_index in tmp_constraint_indexes {
                        let index =
                            match constraint_index_map_reverse.get(&constraint_index) {
                                Some(v) => {
                                    *v
                                },
                                None => {
                                    constraint_index_map.push(constraint_index);
                                    constraint_index_map_reverse.insert(constraint_index, current_constraint_index as u32);
                                    current_constraint_index += 1;
                                    (current_constraint_index - 1) as u32
                                }
                            };

                        pins.push(index);
                    }
                    x_pins.push(pins.len());
                }else{
                    single_variables.insert(variable_in_scope);
                }
            }
        }

        let mut current_partition_label = 0;
        let mut partvec = Vec::new();
        if current_constraint_index == 0 {
            return None;
        }
        for _ in 0..current_constraint_index {
            partvec.push(None);
        }
        let mut to_visit = Vec::new();
        to_visit.push(0);
        loop {
            while !to_visit.is_empty() {
                let constraint_index = to_visit.pop().unwrap();
                if constraint_index as usize >= partvec.len() {
                    println!("test");
                }
                if let Some(label) = partvec.get(constraint_index as usize).unwrap(){
                    if *label != current_partition_label {
                        println!("test");
                    }
                    continue;
                }

                partvec[constraint_index as usize] = Some(current_partition_label);
                let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index_map.get(constraint_index as usize).unwrap()).unwrap();
                for (index, _) in &constraint.unassigned_literals {
                    for i in *x_pins.get(*variable_index_map_reverse.get(index).unwrap() as usize).unwrap()..*x_pins.get(*variable_index_map_reverse.get(index).unwrap() as usize + 1).unwrap() {
                        to_visit.push(*pins.get(i).unwrap());
                    }
                }
            }
            let mut done = true;
            for (i,v) in partvec.iter().enumerate() {
                if v.is_none() {
                    current_partition_label += 1;
                    to_visit.push(i as u32);
                    done = false;
                    break;
                }
            }
            if done {
                break;
            }
        }
        let partvec: Vec<u32> = partvec.iter().map(|x| x.unwrap()).collect();

        if current_partition_label == 0 && single_variables.len() == 0{
            if self.next_variables.is_empty() {
                let (_, _, edges_to_remove) = partition(current_constraint_index as u32, current_variable_index as u32, pins, x_pins);
                for e in edges_to_remove {
                    self.next_variables.push(**variable_index_map.get(e as usize).unwrap() as u32);
                }
           }
            return None;
        }

        let mut component_based_formula = ComponentBasedFormula::new(self.number_unsat_constraints, self.number_unassigned_variables, self.variable_in_scope.clone(), self.constraint_indexes_in_scope.clone());
        let mut number_partitions = 0;
        for p in &partvec {
            if *p > number_partitions {
                number_partitions = *p;
            }
        }
        number_partitions += 1;

        for _ in 0 .. number_partitions {
            component_based_formula.components.push(Component{
                variables: BTreeSet::new(),
                number_unassigned_variables: 0,
                number_unsat_constraints: 0,
                constraint_indexes_in_scope: BTreeSet::new(),
            })
        }
        for (index, partition_number) in partvec.iter().enumerate() {
            let constraint_index = constraint_index_map.get(index).unwrap();
            let component = component_based_formula.components.get_mut(*partition_number as usize).unwrap();
            component.constraint_indexes_in_scope.insert(*constraint_index);
            let constraint = self.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
            for (i,_) in &constraint.unassigned_literals {
                if !component.variables.contains(i) {
                    component.number_unassigned_variables += 1;
                    component.variables.insert(*i);
                }
            }
            if constraint.is_unsatisfied() {
                component.number_unsat_constraints += 1;
            }
        }
        if single_variables.len() > 0 {
            let mut component = Component{
                variables: BTreeSet::new(),
                number_unsat_constraints: 0,
                number_unassigned_variables: 0,
                constraint_indexes_in_scope: BTreeSet::new(),
            };
            for variable_index in single_variables {
                component.variables.insert(*variable_index);
                component.number_unassigned_variables += 1;

            }
            component_based_formula.components.push(component);
        }

        if component_based_formula.previous_number_unassigned_variables as u32 != component_based_formula.components.iter().map(|x| x.number_unassigned_variables).sum() {
            println!("test");
        }
        Some(component_based_formula)
    }

    #[cfg(feature = "show_progress")]
    fn print_progress(&mut self, decision_level: u32) {
        if decision_level < 5 {
            let res = self.progress.get(&decision_level);
            let additional_progress: f32 = 1.0 / self.progress_split as f32;
            match res {
                None => {
                    self.progress.insert(decision_level, additional_progress);
                },
                Some(v) => {
                    self.progress.insert(decision_level, *v + additional_progress);
                }
            }
            for i in decision_level + 1..9{
                self.progress.remove(&i);
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
            literals: BTreeMap::new(),
            sum_true: 0,
            sum_unassigned: 0,
            degree: 1,
            factor_sum: 0,
            hash_value: 0,
            hash_value_old: true,
            constraint_type: GreaterEqual
        };

        for (index, entry) in reason_set_propagated.iter().enumerate() {
            if let Some((a,sign,decision_level)) = entry {
                constraint.literals.insert(index, Literal{
                    index: index as u32,
                    positive: !*sign,
                    factor: 1,
                });
                constraint.assignments.insert(index, (*sign,*a,*decision_level));
                constraint.factor_sum += 1;
            }
        }
        for (index, entry) in reason_set_decision.iter().enumerate() {
            if let Some((a,sign,decision_level)) = entry {
                constraint.literals.insert(index, Literal{
                    index: index as u32,
                    positive: !*sign,
                    factor: 1,
                });
                constraint.assignments.insert(index, (*sign,*a,*decision_level));
                constraint.factor_sum += 1;
            }
        }
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
        assert_eq!(model_count, BigUint::from(18 as u32));
    }

    #[test]
    fn test_ex_2() {
        let opb_file = parsing::parser::parse("x1 + x2 >= 1;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        assert_eq!(model_count, BigUint::from(17 as u32));
    }

    #[test]
    fn test_ex_3() {
        let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from(4080389785 as u32));
    }

    #[test]
    fn test_ex_4() {
        let opb_file = parsing::parser::parse("a + b + c >= 1;\nx + y + z >= 2;\na + x >= 1;\nx1 + x2 + x3 >= 1;\n").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from(175 as u32));
    }

    #[test]
    fn test_ex_5() {
        let file_content = fs::read_to_string("./test_models/financialservices01.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve();
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from(97451212554676 as u128));
    }
}