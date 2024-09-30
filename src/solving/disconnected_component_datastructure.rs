#[derive(Debug)]
pub struct ComponentBasedFormula {
    pub components: Vec<Component>,
    pub current_component: usize,
    pub previous_number_unsat_constraints: usize,
    pub previous_number_unassigned_variables: u32,
    pub previous_variables_in_scope: Vec<bool>,
}

impl ComponentBasedFormula {
    pub fn new(previous_number_unsat_constraints: usize, previous_number_unassigned_variables: u32, previous_variables_in_scope: Vec<bool>) -> ComponentBasedFormula {
        ComponentBasedFormula{
            components: Vec:: new(),
            current_component: 0,
            previous_number_unsat_constraints,
            previous_number_unassigned_variables,
            previous_variables_in_scope
        }
    }
}
#[derive(Debug)]
pub struct Component {
    pub variables: Vec<bool>,
    pub number_unsat_constraints: u32,
    pub number_unassigned_variables: u32,
}