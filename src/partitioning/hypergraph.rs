use std::collections::{BTreeMap, BTreeSet};
use crate::partitioning::disconnected_component_datastructure::{Component, ComponentBasedFormula};
use crate::partitioning::hypergraph_partitioning::partition;
use crate::solving::pseudo_boolean_datastructure::ConstraintIndex::NormalConstraintIndex;
use crate::solving::solver::Solver;

pub struct Hypergraph {
    pub(crate) pins: Vec<u32>,
    pub(crate) x_pins: Vec<u32>,
    pub(crate) variable_index_map: Vec<usize>,
    pub(crate) variable_index_map_reverse: BTreeMap<usize, u32>,
    pub(crate) current_variable_index: u32,
    pub(crate) constraint_index_map: Vec<usize>,
    pub(crate) constraint_index_map_reverse: BTreeMap<usize, u32>,
    pub(crate) current_constraint_index: u32,
    pub(crate) single_variables: BTreeSet<usize>
}

impl Hypergraph {
    pub fn new(solver: &Solver) -> Hypergraph {
        let mut hypergraph = Hypergraph {
            pins: Vec::new(),
            x_pins: Vec::new(),
            variable_index_map: Vec::new(),
            variable_index_map_reverse: BTreeMap::new(),
            current_variable_index: 0,
            constraint_index_map: Vec::new(),
            constraint_index_map_reverse: BTreeMap::new(),
            current_constraint_index: 0,
            single_variables: BTreeSet::new(),
        };
        hypergraph.x_pins.push(0);

        for variable_in_scope in &solver.variable_in_scope {
            if solver.assignments.get(*variable_in_scope).unwrap().is_none() {
                let mut tmp_constraint_indexes = Vec::new();
                for constraint_index in solver.pseudo_boolean_formula.constraints_by_variable.get(*variable_in_scope).unwrap() {
                    let constraint = solver.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
                    if constraint.is_unsatisfied() {
                        if let NormalConstraintIndex(index) = constraint.index {
                            tmp_constraint_indexes.push(index);
                        }
                    }
                }
                if tmp_constraint_indexes.len() > 0 {
                    hypergraph.variable_index_map.push(*variable_in_scope);
                    hypergraph.variable_index_map_reverse.insert(*variable_in_scope, hypergraph.current_variable_index);
                    hypergraph.current_variable_index += 1;
                    for constraint_index in tmp_constraint_indexes {
                        let index =
                            match hypergraph.constraint_index_map_reverse.get(&constraint_index) {
                                Some(v) => {
                                    *v
                                },
                                None => {
                                    hypergraph.constraint_index_map.push(constraint_index);
                                    hypergraph.constraint_index_map_reverse.insert(constraint_index, hypergraph.current_constraint_index as u32);
                                    hypergraph.current_constraint_index += 1;
                                    (hypergraph.current_constraint_index - 1) as u32
                                }
                            };

                        hypergraph.pins.push(index);
                    }
                    hypergraph.x_pins.push(hypergraph.pins.len() as u32);
                } else {
                    hypergraph.single_variables.insert(*variable_in_scope);
                }
            }
        }

        hypergraph
    }

    pub fn find_disconnected_components(&self, solver: &Solver) -> Option<Vec<u32>> {
        let mut current_partition_label = 0;
        let mut partvec = Vec::new();
        let mut number_visited = 0;
        let mut last_visited = 0;
        if self.current_constraint_index <= 1 {
            return None;
        }
        for _ in 0..self.current_constraint_index {
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
                if partvec.get(constraint_index as usize).is_none(){
                    println!("{}", constraint_index);
                    println!("{}", self.current_constraint_index);
                }
                if let Some(label) = partvec.get(constraint_index as usize).unwrap() {
                    if *label != current_partition_label {
                        println!("test");
                    }
                    continue;
                }
                number_visited += 1;
                partvec[constraint_index as usize] = Some(current_partition_label);
                let constraint = solver.pseudo_boolean_formula.constraints.get(*self.constraint_index_map.get(constraint_index as usize).unwrap()).unwrap();
                for (index, _) in &constraint.unassigned_literals {
                    let hg_index = *self.variable_index_map_reverse.get(index).unwrap() as usize;
                    for i in *self.x_pins.get(hg_index).unwrap()..*self.x_pins.get(hg_index + 1).unwrap() {
                        to_visit.push(*self.pins.get(i as usize).unwrap());
                    }
                }
            }
            if number_visited == partvec.len() {
                break;
            }
            for i in last_visited..partvec.len() {
                let v = partvec.get(i).unwrap();
                if v.is_none() {
                    current_partition_label += 1;
                    to_visit.push(i as u32);
                    last_visited = i;
                    break;
                }
            }
        }
        let partvec: Vec<u32> = partvec.iter().map(|x| x.unwrap()).collect();
        if current_partition_label == 0 && self.single_variables.len() == 0 {
            return None;
        } else {
            Some(partvec)
        }
    }

    pub fn get_variables_for_cut(&self) -> Vec<u32> {
        if self.current_constraint_index <= 1 || self.current_variable_index <= 1 {
            return Vec::new()
        }
        let mut next_variables = Vec::new();
        let (_, _, edges_to_remove) = partition(self.current_constraint_index, self.current_variable_index, &self.pins, &self.x_pins);
        for e in edges_to_remove {
            next_variables.push(*self.variable_index_map.get(e as usize).unwrap() as u32);
        }
        next_variables
    }


    pub fn create_partition(&self, solver: &Solver, partvec: Vec<u32>) -> ComponentBasedFormula {
        let mut component_based_formula = ComponentBasedFormula::new(solver.number_unsat_constraints, solver.number_unassigned_variables, solver.variable_in_scope.clone(), solver.constraint_indexes_in_scope.clone());
        let mut number_partitions = 0;
        for p in &partvec {
            if *p > number_partitions {
                number_partitions = *p;
            }
        }
        number_partitions += 1;

        for _ in 0..number_partitions {
            component_based_formula.components.push(Component {
                variables: BTreeSet::new(),
                number_unassigned_variables: 0,
                number_unsat_constraints: 0,
                constraint_indexes_in_scope: BTreeSet::new(),
            })
        }
        for (index, partition_number) in partvec.iter().enumerate() {
            let constraint_index = self.constraint_index_map.get(index).unwrap();
            let component = component_based_formula.components.get_mut(*partition_number as usize).unwrap();
            component.constraint_indexes_in_scope.insert(*constraint_index);
            let constraint = solver.pseudo_boolean_formula.constraints.get(*constraint_index).unwrap();
            for (i, _) in &constraint.unassigned_literals {
                if !component.variables.contains(i) {
                    component.number_unassigned_variables += 1;
                    component.variables.insert(*i);
                }
            }
            if constraint.is_unsatisfied() {
                component.number_unsat_constraints += 1;
            }
        }
        if self.single_variables.len() > 0 {
            let mut component = Component {
                variables: BTreeSet::new(),
                number_unsat_constraints: 0,
                number_unassigned_variables: 0,
                constraint_indexes_in_scope: BTreeSet::new(),
            };
            for variable_index in &self.single_variables {
                component.variables.insert(*variable_index);
                component.number_unassigned_variables += 1;
            }
            component_based_formula.components.push(component);
        }

        if component_based_formula.previous_number_unassigned_variables as u32 != component_based_formula.components.iter().map(|x| x.number_unassigned_variables).sum() {
            println!("test");
        }
        component_based_formula
    }
}