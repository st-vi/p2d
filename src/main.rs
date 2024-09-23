mod parsing {
    pub mod parser;
    pub mod equation_datastructure;
}

mod solving {
    pub mod pseudo_boolean_datastructure;
}


fn main() {
    parsing::parser::parse("x1 + x2 = 7;");
}
