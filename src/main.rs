use std::collections::HashSet;
use std::fs;
use std::hash::{DefaultHasher, Hash, Hasher};
use crate::solving::pseudo_boolean_datastructure::{Constraint, Literal, PseudoBooleanFormula};
use crate::solving::recursive_solving::RecSolver;
use crate::solving::solver::Solver;

mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
    pub mod solver;
    pub mod recursive_solving;
}

fn main() {
    let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);


}
