use crate::solving::pseudo_boolean_datastructure::PseudoBooleanFormula;

mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
    pub mod solver;
}


fn main() {
    let opb_file = parsing::parser::parse("x1 + x2 >= 7;\n x1 + x3 >= 2").expect("error while parsing");
    let _formula = PseudoBooleanFormula::new(&opb_file);
    println!("test");
}
