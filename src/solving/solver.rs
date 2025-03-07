use std::cmp::PartialEq;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::rc::Rc;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use crate::partitioning::disconnected_component_datastructure::{ComponentBasedFormula};
use crate::partitioning::hypergraph::Hypergraph;
use crate::solving::ddnnf::{DDNNFLiteral, DDNNFNode, DDNNF};
use crate::solving::ddnnf::DDNNFNode::{AndNode, FalseLeave, LiteralLeave, TrueLeave};
use crate::solving::pseudo_boolean_datastructure::{calculate_hash, Constraint, ConstraintIndex, Literal, PseudoBooleanFormula};
use crate::solving::pseudo_boolean_datastructure::ConstraintIndex::{LearnedClauseIndex, NormalConstraintIndex};
use crate::solving::pseudo_boolean_datastructure::ConstraintType::GreaterEqual;
use crate::solving::pseudo_boolean_datastructure::PropagationResult::*;
use crate::solving::solver::AssignmentKind::{FirstDecision, Propagated, SecondDecision};
use crate::solving::solver::AssignmentStackEntry::{Assignment, ComponentBranch};

pub struct Solver {
    pub(crate) pseudo_boolean_formula: PseudoBooleanFormula,
    assignment_stack: Vec<AssignmentStackEntry>,
    pub(crate) assignments: Vec<Option<(u32, bool)>>,
    decision_level: u32,
    learned_clauses: Vec<Constraint>,
    learned_clauses_by_variables: Vec<Vec<usize>>,
    result_stack: Vec<BigUint>,
    ddnnf_stack: Vec<Rc<DDNNFNode>>,
    pub(crate) number_unsat_constraints: usize,
    pub(crate) number_unassigned_variables: u32,
    cache: HashMap<u64,(BigUint, Rc<DDNNFNode>)>,
    pub statistics: Statistics,
    pub(crate) variable_in_scope: BTreeSet<usize>,
    pub(crate) constraint_indexes_in_scope: BTreeSet<usize>,
    progress: HashMap<u32, f32>,
    last_progress: f32,
    pub(crate) next_variables: Vec<u32>,
    progress_split: u128,
    vsids_scores: Vec<f64>,
    dlcs_scores: Vec<f64>,
    unique_id: u32
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
            ddnnf_stack: Vec::new(),
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
            progress_split: 1,
            vsids_scores: Vec::new(),
            dlcs_scores: Vec::new(),
            unique_id: 0,
        };
        for i in 0..number_variables{
            solver.assignments.push(None);
            solver.variable_in_scope.insert(i as usize);
            solver.learned_clauses_by_variables.push(Vec::new());
            solver.vsids_scores.push(1.0);
            solver.dlcs_scores.push(0.0);
        }
        for c in &solver.pseudo_boolean_formula.constraints {
            if let NormalConstraintIndex(i) = c.index {
                solver.constraint_indexes_in_scope.insert(i);
            }
            for (i,l) in &c.literals {
                solver.dlcs_scores[*i] = l.factor as f64/c.degree as f64;
            }
        }
        solver
    }

    fn update_dlcs_scores(&mut self) {
        for c in &self.pseudo_boolean_formula.constraints {
            for (i,l) in &c.literals {
                if c.is_unsatisfied(){
                    self.dlcs_scores[*i] = l.factor as f64/ (c.degree - c.sum_true as i128)as f64;
                }

            }
        }
    }

    fn get_unique_id(&mut self) -> u32 {
        self.unique_id += 1;
        self.unique_id -1
    }

    pub fn solve(&mut self) -> SolverResult {
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

    fn count(&mut self) -> SolverResult {
        if !self.simplify(){
            //after simplifying formula violated constraint detected
            return SolverResult{
                model_count: BigUint::zero(),
                ddnnf: DDNNF{
                    root_node: Rc::new(FalseLeave),
                    number_variables: self.pseudo_boolean_formula.number_variables
                }
            };
        }

        loop {
            if self.number_unsat_constraints <= 0 {
                //current assignment satisfies all constraints
                self.result_stack.push(BigUint::from(2 as u32).pow(self.number_unassigned_variables));
                self.ddnnf_stack.push(Rc::new(TrueLeave));
                self.next_variables.clear();
                if !self.backtrack(){
                    //nothing to backtrack to, we searched the whole space
                    return SolverResult{
                        model_count: self.result_stack.pop().unwrap(),
                        ddnnf: DDNNF{
                            root_node: self.ddnnf_stack.pop().unwrap(),
                            number_variables: self.pseudo_boolean_formula.number_variables
                        }
                    };
                }
                continue
            }

            #[cfg(feature = "cache")]
            {
                let cached_result = self.get_cached_result();
                if let Some((mc, ddnnf_ref)) = cached_result {
                    self.ddnnf_stack.push(Rc::clone(&ddnnf_ref));
                    self.result_stack.push(mc);
                    self.next_variables.clear();
                    self.statistics.cache_hits += 1;
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return SolverResult{
                            model_count: self.result_stack.pop().unwrap(),
                            ddnnf: DDNNF{
                                root_node: self.ddnnf_stack.pop().unwrap(),
                                number_variables: self.pseudo_boolean_formula.number_variables
                            }
                        };
                    }
                    continue;
                }
            }

            #[cfg(feature = "disconnected_components")]
            {


                if self.branch_components() {
                    continue;
                }
            }

            let decided_literal = self.decide();
            match decided_literal {
                None => {
                    //there are no free variables to assign a value to
                    self.result_stack.push(BigUint::zero());
                    self.ddnnf_stack.push(Rc::new(FalseLeave));
                    self.next_variables.clear();
                    if !self.backtrack(){
                        //nothing to backtrack to, we searched the whole space
                        return SolverResult{
                            model_count: self.result_stack.pop().unwrap(),
                            ddnnf: DDNNF{
                                root_node: self.ddnnf_stack.pop().unwrap(),
                                number_variables: self.pseudo_boolean_formula.number_variables
                            }
                        };
                    }
                },
                Some((var_index, var_sign)) => {
                    //set and propagate the new decided variable
                    if let Some(constraint_index) = self.propagate(var_index, var_sign, FirstDecision) {
                        //at least one constraint violated
                        #[cfg(feature = "clause_learning")]
                        self.safe_conflict_clause(constraint_index);

                        self.result_stack.push(BigUint::zero());
                        self.ddnnf_stack.push(Rc::new(FalseLeave));

                        self.next_variables.clear();
                        if !self.backtrack(){
                            //nothing to backtrack to, we searched the whole space
                            return SolverResult{
                                model_count: self.result_stack.pop().unwrap(),
                                ddnnf: DDNNF{
                                    root_node: self.ddnnf_stack.pop().unwrap(),
                                    number_variables: self.pseudo_boolean_formula.number_variables
                                }
                            };
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
                    if let ConstraintIndex::NormalConstraintIndex(index) = constraint.index {
                        self.constraint_indexes_in_scope.remove(&index);
                    }
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
/*
        for clause in &mut self.learned_clauses {
            let mut flag = false;
            for constraint_index in self.learned_clauses_by_variables.get(variable_index as usize).unwrap() {
                if let LearnedClauseIndex(i) = clause.index {
                    if *constraint_index == i {
                        flag = true;
                        break;
                    }
                }
            }
            if flag {
                //break;
            }

            if clause.literals.contains_key(&(variable_index as usize)) {
                continue;
            }
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
                    self.statistics.tmp_count += 1;
                    propagation_queue.push_back((l.index, l.positive, Propagated(*constraint_index), true));
                },
                NothingToPropagated => {

                },
                AlreadySatisfied => {

                },
                ImpliedLiteralList(list) => {
                    self.statistics.tmp_count += 1;
                    /*
                    println!("decision_level: {}, variable_index: {}", self.decision_level, variable_index);
                    for (i, (s,kind,dl)) in &clause.assignments {
                        println!("i: {}, s: {}, k: {:?}, dl: {}", i, s, kind, dl);
                    }

                     */
                    for l in list {
                        propagation_queue.push_back((l.index, l.positive, Propagated(*constraint_index), true));
                    }
                }
            }
        }


 */

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
                    panic!("Assigning a two different values to a single variable should never happen")
                }
            }
            if from_learned_clause {
                self.statistics.propagations_from_learned_clauses += 1;
            }
            self.number_unassigned_variables -= 1;
            self.variable_in_scope.remove(&(index as usize));
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
                        self.constraint_indexes_in_scope.remove(&constraint_index);
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
            let node_id = self.get_unique_id();
            if let Some(top_element) = self.assignment_stack.last() {
                match top_element {
                    Assignment(last_assignment) => {
                        if last_assignment.decision_level == 0{
                            let ddnnf_node = self.ddnnf_stack.pop().unwrap();
                            if matches!(*ddnnf_node, FalseLeave){
                                self.ddnnf_stack.push(Rc::new(FalseLeave));
                                return false;
                            }
                            if let AndNode(child_list,_) = (*ddnnf_node).clone() {
                                let mut new_child_list = Vec::new();
                                let mut contains_false = false;
                                for node in child_list {
                                    new_child_list.push(node.clone());
                                    if matches!(*node, FalseLeave){
                                        contains_false = true;
                                        break;
                                    }
                                }
                                if contains_false {
                                    self.ddnnf_stack.push(Rc::from(FalseLeave));
                                }else{
                                    new_child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{index: last_assignment.variable_index, positive: last_assignment.variable_sign}))));
                                    let node_id = self.get_unique_id();
                                    self.ddnnf_stack.push(Rc::new(AndNode(new_child_list, node_id)));
                                }

                            }else {
                                let mut child_list = Vec::new();
                                child_list.push(ddnnf_node);
                                child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{index: last_assignment.variable_index, positive: last_assignment.variable_sign}))));
                                let and_node = AndNode(child_list, self.get_unique_id());
                                self.ddnnf_stack.push(Rc::new(and_node));
                            }
                            self.undo_last_assignment();
                        }else if let Propagated(_) = last_assignment.assignment_kind {
                            let ddnnf_node = self.ddnnf_stack.pop().unwrap();
                            if let AndNode(child_list,_) = (*ddnnf_node).clone() {
                                let mut new_child_list = Vec::new();
                                for node in child_list {
                                    new_child_list.push(node.clone());
                                }
                                new_child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{index: last_assignment.variable_index, positive: last_assignment.variable_sign}))));
                                let node_id = self.get_unique_id();
                                self.ddnnf_stack.push(Rc::new(AndNode(new_child_list, node_id)));
                            }else if let FalseLeave = (*ddnnf_node).clone() {
                                self.ddnnf_stack.push(Rc::new(FalseLeave));
                            }
                            else{
                                let mut child_list = Vec::new();
                                if !matches!(*ddnnf_node, TrueLeave) {
                                    child_list.push(ddnnf_node);
                                }
                                child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{index: last_assignment.variable_index, positive: last_assignment.variable_sign}))));
                                let and_node = AndNode(child_list, self.get_unique_id());
                                self.ddnnf_stack.push(Rc::new(and_node));
                            }
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
                                self.ddnnf_stack.push(Rc::new(FalseLeave));

                            }else{
                                return true;
                            }
                        }else if last_assignment.assignment_kind == SecondDecision {
                            let r1 = self.result_stack.pop().unwrap();
                            let r2 = self.result_stack.pop().unwrap();
                            let res = r1+r2;
                            self.result_stack.push(res.clone());

                            let mut d1 = self.ddnnf_stack.pop().unwrap();
                            if let TrueLeave = *d1 {
                                d1 = Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                    index: last_assignment.variable_index,
                                    positive: last_assignment.variable_sign,
                                })));
                            }else if !matches!(*d1, FalseLeave){
                                if let AndNode(child_list,_) = (*d1).clone() {
                                    let mut new_child_list = Vec::new();
                                    for child in child_list {
                                        new_child_list.push(child);
                                    }
                                    new_child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                        index: last_assignment.variable_index,
                                        positive: last_assignment.variable_sign,
                                    }))));
                                    d1 = Rc::new(AndNode(new_child_list, node_id));
                                }else {
                                    let mut child_list = Vec::new();
                                    child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                        index: last_assignment.variable_index,
                                        positive: last_assignment.variable_sign,
                                    }))));
                                    child_list.push(d1);
                                    d1 = Rc::new(AndNode(child_list, node_id));
                                }
                            }


                            let mut d2 = self.ddnnf_stack.pop().unwrap();
                            if let TrueLeave = *d2 {
                                d2 = Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                    index: last_assignment.variable_index,
                                    positive: !last_assignment.variable_sign,
                                })));
                            }else if !matches!(*d2, FalseLeave) {
                                if let AndNode(child_list,_) = (*d2).clone() {
                                    let mut new_child_list = Vec::new();
                                    for child in child_list {
                                        new_child_list.push(child);
                                    }
                                    new_child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                        index: last_assignment.variable_index,
                                        positive: !last_assignment.variable_sign,
                                    }))));
                                    d2 = Rc::new(AndNode(new_child_list,self.get_unique_id()));
                                }else {
                                    let mut child_list = Vec::new();
                                    child_list.push(Rc::new(LiteralLeave(Rc::new(DDNNFLiteral{
                                        index: last_assignment.variable_index,
                                        positive: !last_assignment.variable_sign,
                                    }))));
                                    child_list.push(d2);
                                    d2 = Rc::new(AndNode(child_list,self.get_unique_id()));
                                }
                            }

                            let d_res;
                            if matches!(*d1, FalseLeave) && matches!(*d2, FalseLeave) {
                                d_res = Rc::new(FalseLeave);
                            }else if matches!(*d2, FalseLeave) {
                                d_res = d1;
                            }else if matches!(*d1, FalseLeave) {
                                d_res = d2;
                            }else{
                                d_res = Rc::new(DDNNFNode::OrNode(
                                    vec![d1,d2],
                                    self.get_unique_id()
                                ));
                            }
                            let ddnnf_ref = d_res.clone();
                            self.ddnnf_stack.push(d_res);

                            self.next_variables.clear();
                            self.decision_level -= 1;

                            self.undo_last_assignment();

                            #[cfg(feature = "cache")]
                            self.cache(res, ddnnf_ref);
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
                            let mut zero_flag = false;
                            let mut child_nodes = Vec::new();
                            for _ in 0..last_branch.components.len(){
                                branch_result = branch_result * self.result_stack.pop().unwrap();
                                let child_node = self.ddnnf_stack.pop().unwrap();
                                if let FalseLeave = *child_node {
                                    zero_flag = true;
                                }
                                child_nodes.push(child_node);
                            }
                            let ddnnf_node = if zero_flag {FalseLeave} else { AndNode(child_nodes, node_id) };
                            self.ddnnf_stack.push(Rc::new(ddnnf_node));

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
            self.variable_in_scope.insert(last_assignment.variable_index as usize);
            //undo in constraints
            for constraint_index in self.pseudo_boolean_formula.constraints_by_variable.get(last_assignment.variable_index as usize).unwrap() {
                let constraint = self.pseudo_boolean_formula.constraints.get_mut(*constraint_index).unwrap();
                if constraint.assignments.get(&(last_assignment.variable_index as usize)).is_some() {
                    //self.dlcs_scores[last_assignment.variable_index as usize] = self.dlcs_scores[last_assignment.variable_index as usize] + constraint.literals.get(&(last_assignment.variable_index as usize)).unwrap().factor as f64 / constraint.degree as f64;
                }
                if constraint.undo(last_assignment.variable_index, last_assignment.variable_sign) {
                    self.number_unsat_constraints += 1;
                    self.constraint_indexes_in_scope.insert(*constraint_index);
                }
            }
            //undo in learned clauses
            for constraint_index in self.learned_clauses_by_variables.get(last_assignment.variable_index as usize).unwrap() {
                let constraint = self.learned_clauses.get_mut(*constraint_index).unwrap();
                constraint.undo(last_assignment.variable_index, last_assignment.variable_sign);
            }
        }
    }

    fn scale_vector(input: &mut [f64], factor: f64) {
        input.iter_mut().for_each(|x| *x *= factor);
    }

    fn get_next_variable(&mut self) -> Option<u32> {

        //TODO only necessary if the scores are used, otherwise just decreases the performance
        //Self::scale_vector(&mut self.vsids_scores, 0.8);
        //self.update_dlcs_scores();

        if self.next_variables.len() == 1 {
            return self.next_variables.pop();
        }

        if self.next_variables.len() > 0 {
            let mut max_index: Option<u32> = None;
            let mut max_value: Option<f64> = None;
            for k in &self.next_variables {
                if *self.dlcs_scores.get(*k as usize).unwrap() < 0.0 {
                    panic!("test")
                }
                let v = *self.vsids_scores.get(*k as usize).unwrap();//0.2 * *self.dlcs_scores.get(*k as usize).unwrap() + 0.8 * *self.vsids_scores.get(*k as usize).unwrap();
                if max_value.is_none() {
                    max_value = Some(v);
                    max_index = Some(*k);
                } else if let Some(value) = max_value {
                    if v > value {
                        max_value = Some(v);
                        max_index = Some(*k);
                    }
                }
            }
            if let Some(_) = max_index {
                return max_index;
            }else {
                self.next_variables.clear();
            }
        }

        let mut max_index: Option<u32> = None;
        let mut max_value: Option<f64> = None;

        for constraint in &self.pseudo_boolean_formula.constraints {
            if constraint.is_unsatisfied(){
                for (_,literal) in &constraint.unassigned_literals {
                    if self.variable_in_scope.contains(&(literal.index as usize)) {
                        let k = literal.index;
                        let v = *self.vsids_scores.get(k as usize).unwrap();//0.2 *self.dlcs_scores.get(k as usize).unwrap()+ 0.8 * *self.vsids_scores.get(k as usize).unwrap();
                        if max_value.is_none() {
                            max_value = Some(v);
                            max_index = Some(k);
                        } else if let Some(value) = max_value {
                            if v > value {
                                max_value = Some(v);
                                max_index = Some(k);
                            }
                        }
                    }
                }
            }
        }
        if let Some(_) = max_index {
            return max_index;
        }else {
            return None;
        }
    }

    #[cfg(feature = "cache")]
    fn cache(&mut self, mc: BigUint, ddnnf_ref: Rc<DDNNFNode>) {
        if self.number_unsat_constraints > 0 {
            self.cache.insert(calculate_hash(&self.variable_in_scope, &self.assignments, &mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.constraint_indexes_in_scope), (mc, ddnnf_ref));
            self.statistics.cache_entries += 1;
        }
    }

    #[cfg(feature = "cache")]
    fn get_cached_result(&mut self) -> Option<(BigUint, Rc<DDNNFNode>)> {
        match self.cache.get(&calculate_hash(&self.variable_in_scope, &self.assignments,&mut self.pseudo_boolean_formula, self.number_unassigned_variables, &self.constraint_indexes_in_scope)) {
            None => None,
            Some((mc, ddnnf_ref)) => Some((mc.clone(), Rc::clone(ddnnf_ref)))
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
        self.next_variables = self.next_variables.iter().filter(|x| self.assignments.get(**x as usize).unwrap().is_none() && self.variable_in_scope.contains(&(**x as usize))).map(|x| *x).collect();

        if self.number_unsat_constraints > 1 {
            let hypergraph = Hypergraph::new(&self);
            match hypergraph.find_disconnected_components(&self) {
                Some(partvec) => {
                    // there is already a partition
                    Some(hypergraph.create_partition(&self, partvec))
                },
                None => {
                    // currently no partition => get variables for a good cut
                    if self.next_variables.is_empty() {
                        let nv = hypergraph.get_variables_for_cut();
                        self.next_variables.extend(nv);
                    }

                    None
                }
            }
        } else {
            None
        }
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
    fn analyze(&mut self, conflicting_variable_indexes: &BTreeMap<usize,(AssignmentKind, bool, u32)>) -> Option<Constraint> {
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
            constraint_type: GreaterEqual,
            max_literal: Literal{
                index: 0,
                factor: 0,
                positive: false,
            },
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
        for (_,literal) in &constraint.literals {
            let mut tmp = *self.vsids_scores.get(literal.index as usize).unwrap();
            tmp += literal.factor as f64 / (constraint.degree - constraint.sum_true as i128) as f64;
            self.vsids_scores[literal.index as usize] = tmp;
        }
        constraint.max_literal = constraint.get_max_literal();
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

pub struct SolverResult {
    pub(crate) model_count: BigUint,
    pub(crate) ddnnf: DDNNF,
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::str::FromStr;
    use serial_test::serial;
    use crate::parsing;
    use crate::solving::ddnnf::DDNNFPrinter;
    use super::*;

    #[test]
    #[serial]
    fn test_ex_1() {
        let opb_file = parsing::parser::parse("#variable= 5 #constraint= 2\nx1 + x2 >= 0;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(18 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_2() {
        let opb_file = parsing::parser::parse("#variable= 5 #constraint= 2\nx1 + x2 >= 1;\n3 x2 + x3 + x4 + x5 >= 3;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(17 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_3() {
        let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        //let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new(), edge_counter: 0, node_counter: 0};
        //let ddnnf = printer.print();
        //let ddnnf = result.ddnnf.get_d4_string_representation();
        //fs::write("berkely_p2d.d4", ddnnf);
        let model_count = result.model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from_str(&"63552545718785").unwrap());
    }

    #[test]
    #[serial]
    fn test_ex_4() {
        let file_content = fs::read_to_string("./test_models/financialservices01.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from_str("97451212554676").unwrap());
    }

    #[test]
    #[serial]
    fn test_ex_5() {
        let opb_file = parsing::parser::parse("#variable= 3 #constraint= 1\n2 x + y + z >= 2;\n").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        //let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new()};
        //let ddnnf = printer.print();
        //let ddnnf = result.ddnnf.get_d4_string_representation();
        //fs::write("test.d4", ddnnf);
        let model_count = result.model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from(5 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_6() {
        let file_content = fs::read_to_string("./test_models/automotive2_4.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        //let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new()};
        //let ddnnf = printer.print();
        //let ddnnf = result.ddnnf.get_d4_string_representation();
        //fs::write("automotive2_p2d.d4", ddnnf);
        let model_count = result.model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from_str("16505272636520770608049807336686263419262278171474896528902674080188226535986513386206222739154199990312304316432375708419908334951120777840761446056501033491673756322502123336090943486436039243372030766943458602037261070847529674534356018156008670682187009867114669183165589812678347677020009178324343716516097209109845184348679968274326123049227527790019157116786715333025963056661497445641173800199765222163167371496529076598275345593840432679060593082091562556148743367163011059914376453848874833624216454940443543476903147239713725910883379897186772787280371367887760273478656423910102759489682512679566900002943975655597096674268679680101882972677272515371297444691753104874195657464993976495326679318657622295700861777088118982149971100416087768578981508055766733740078413795875538473667538095783126142950285621270589214044781390019682483886583359849938540211221775670172765581722321182214883760887169041797021188330713322356432125673511102447057280896884295376155649470685335338495258057322025865111781429202794739966258303407257483764514048109066413495739887120721093956731137104071984616616093530304438776638066291197761951034921410607293591331155786344517409313802138987056145557947322022252231548896287559556403966183750725000574198535237943080891660398515976002019199247649442832823641555125736303883310186456855445612857146873733447167431344738817867253190162116602107467483579427839512688474377395370679756390400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap());
    }

    #[test]
    #[serial]
    fn test_ex_7() {
        let file_content = fs::read_to_string("./test_models/automotive01.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        //let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new()};
        //let ddnnf = printer.print();
        //let ddnnf = result.ddnnf.get_d4_string_representation();
        //fs::write("automotive2_p2d.d4", ddnnf);
        let model_count = result.model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from_str("54337953889526644797436357304783500234473556203012469981705794070419609376066883019863858681556047971579366711252721976681982553481954710208375451836305175948768348959659511355551303323044387225600000000000000000000000").unwrap());
    }

    #[test]
    #[serial]
    fn test_ex_8() {
        let file_content = fs::read_to_string("./test_models/busybox.opb").expect("cannot read file");
        let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        //let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new()};
        //let ddnnf = printer.print();
        //let ddnnf = result.ddnnf.get_d4_string_representation();
        //fs::write("automotive2_p2d.d4", ddnnf);
        let model_count = result.model_count;
        println!("{:#?}", solver.statistics);
        assert_eq!(model_count, BigUint::from_str("3599239755983329331332100508562451780508192148493160801718199944973008026807919208513108710328389951098075842967611059200000000000000000000000").unwrap());
    }

    #[test]
    #[serial]
    fn test_ex_9() {
        let opb_file = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 = 1;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(2 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_10() {
        let opb_file = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 < 2;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(3 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_11() {
        let opb_file = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 > 1;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(1 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_12() {
        let opb_file = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 != 1;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let model_count = solver.solve().model_count;
        assert_eq!(model_count, BigUint::from(2 as u32));
    }

    #[test]
    #[serial]
    fn test_ex_13() {
        let opb_file = parsing::parser::parse("#variable= 1 #constraint= 1\nx1 >= 0;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new(), edge_counter: 0, node_counter: 0};
        let ddnnf = printer.print();
        assert_eq!(ddnnf, "t 1 0\n");
    }

    #[test]
    #[serial]
    fn test_ex_14() {
        let opb_file = parsing::parser::parse("#variable= 1 #constraint= 1\nx1 > 1;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new(), edge_counter: 0, node_counter: 0};
        let ddnnf = printer.print();
        assert_eq!(ddnnf, "o 1 0\nf 2 0\n1 2 1 0\n");
    }

    #[test]
    #[serial]
    fn test_ex_15() {
        let opb_file = parsing::parser::parse("#variable= 2 #constraint= 1\nx1 + x2 >= 1;").expect("error while parsing");
        let formula = PseudoBooleanFormula::new(&opb_file);
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new(), edge_counter: 0, node_counter: 0};
        let ddnnf = printer.print();
        assert_eq!(ddnnf, "o 1 0\nt 2 0\n1 2 2 -1 0\n1 2 1 0\n");
    }
}