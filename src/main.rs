use std::fs;
use num_bigint::BigUint;
use crate::partitioning::hypergraph_partitioning::partition;
use crate::solving::pseudo_boolean_datastructure::PseudoBooleanFormula;
use crate::solving::solver::Solver;

mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
    pub mod solver;
}

mod partitioning {
    pub mod patoh_api;
    pub mod hypergraph_partitioning;
    pub mod disconnected_component_datastructure;
}

fn main() {
    run_not_rec();
}

fn run_not_rec(){
    //let file_content = fs::read_to_string("/home/stefan/stefan-vill-master/tmp_eval/tmp5.opb").expect("cannot read file");
    //let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
    let file_content = fs::read_to_string("./test_models/financialservices01.opb").expect("cannot read file");
    //let file_content = "x3 >= 0;\n-x1 + 2 x2 >= 1;\n-x2 -2 x1 >= -1;\n".to_string();
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);


}
