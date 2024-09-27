use std::fs;
use crate::solving::pseudo_boolean_datastructure::PseudoBooleanFormula;
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
    run_rec();
    run_not_rec();
}

fn run_rec(){
    let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = RecSolver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);
}

fn run_not_rec(){
    let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);
}
