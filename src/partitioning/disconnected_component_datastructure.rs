use std::collections::BTreeSet;

#[derive(Debug, Clone)]
pub struct ComponentBasedFormula {
    pub components: Vec<Component>,
    pub current_component: usize,
    pub previous_number_unsat_constraints: usize,
    pub previous_number_unassigned_variables: u32,
    pub previous_variables_in_scope: BTreeSet<usize>,
    pub previous_constraint_indexes_in_scope: BTreeSet<usize>,
}

impl ComponentBasedFormula {
    pub fn new(previous_number_unsat_constraints: usize, previous_number_unassigned_variables: u32, previous_variables_in_scope: BTreeSet<usize>, previous_constraint_indexes_in_scope: BTreeSet<usize>) -> ComponentBasedFormula {
        ComponentBasedFormula{
            components: Vec:: new(),
            current_component: 0,
            previous_number_unsat_constraints,
            previous_number_unassigned_variables,
            previous_variables_in_scope,
            previous_constraint_indexes_in_scope
        }
    }
}
#[derive(Debug, Clone)]
pub struct Component {
    pub constraint_indexes_in_scope: BTreeSet<usize>,
    pub variables: BTreeSet<usize>,
    pub number_unsat_constraints: u32,
    pub number_unassigned_variables: u32,
}