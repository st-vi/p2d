use std::fs;
use crate::solving::pseudo_boolean_datastructure::PseudoBooleanFormula;
use crate::solving::solver::AssignmentKind::FirstDecision;
use crate::solving::solver::Solver;

mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
    pub mod disconnected_component_datastructure;
    pub mod solver;
}

fn main() {
    run_not_rec();
    test();
}

fn test() {
    let opb_file = parsing::parser::parse("a + b + c >= 1;\nx + y + z >= 2;\na + x >= 1;\nx1 + x2 + x3 >= 1;\n").expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    solver.propagate(3,true,FirstDecision);
    //let component_based_formula = solver.to_disconnected_components(solver);
    //println!("{:#?}", component_based_formula);

}

fn run_not_rec(){
    let file_content = fs::read_to_string("/home/stefan/stefan-vill-master/tmp_eval/tmp5.opb").expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);
}
