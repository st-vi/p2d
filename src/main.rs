use std::{fs};
use std::collections::HashMap;
use clap::{Arg, Command};
use clap::builder::Str;
use crate::solving::ddnnf::DDNNFPrinter;
use crate::solving::pseudo_boolean_datastructure::PseudoBooleanFormula;
use crate::solving::solver::Solver;

mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
    pub mod solver;
    pub mod ddnnf;
}

mod partitioning {
    pub mod patoh_api;
    pub mod hypergraph_partitioning;
    pub mod disconnected_component_datastructure;
    pub mod hypergraph;
}

fn main() {

    let matches = Command::new("p2d")
        .version("1.0")
        .about("Transforms a set of pseudo-boolean constraints into d d-DNNF (and calculates the model count)")
        .arg(
            Arg::new("input")
                .required(true)
                .value_name("INPUT_FILE")
                .help("Path to the input file"),
        )
        .arg(
            Arg::new("mode")
                .short('m')
                .long("mode")
                .value_name("MODE")
                .help("Mode of operation: mc (default) or ddnnf")
                .default_value("mc")
                .value_parser(["mc", "ddnnf"]),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .long("output")
                .value_name("OUTPUT_FILE")
                .help("Path to the output file (required if mode is ddnnf)"),
        )
        .get_matches();

    let input_file = matches.get_one::<String>("input").unwrap();
    let mode = matches.get_one::<String>("mode").unwrap();
    let optional_output_file = matches.get_one::<String>("output");

    run_not_rec(input_file, mode, optional_output_file);











    //run_not_rec("./test_models/financialservices01.opb", "ddnnf", Some(&String::from("/home/stefan/test/p2d.nnf")));

}

fn run_not_rec(input_path: &str, mode: &str, output_file: Option<&String>){
    let file_content = fs::read_to_string(input_path).expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let result = solver.solve();
    let model_count = result.model_count;
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);
    if mode == "ddnnf" {
        if output_file.is_none() {
            panic!("Missing output file!")
        }
        let mut printer = DDNNFPrinter{true_sink_id: None, false_sink_id: None, ddnnf: result.ddnnf, current_node_id: 0, id_map: HashMap::new(), edge_counter: 0, node_counter: 0};
        let ddnnf = printer.print();
        fs::write(output_file.unwrap(), ddnnf).expect("Error while writing outputfile");
    }



}
