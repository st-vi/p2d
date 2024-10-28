use bimap::{BiHashMap, BiMap};

pub struct OPBFile {
    pub name_map: BiMap<String, u32>,
    pub equations: Vec<Equation>,
    pub max_name_index: u32,
    pub number_constraints: usize,
    pub number_variables: usize,
}

impl OPBFile {
    pub fn new() -> OPBFile {
        OPBFile {
            name_map: BiHashMap::new(),
            equations: Vec::new(),
            max_name_index: 0,
            number_constraints: 0,
            number_variables: 0,
        }
    }
}
#[derive(Clone)]
pub struct Equation {
    pub lhs: Vec<Summand>,
    pub rhs: i128,
    pub kind: EquationKind
}

#[derive(PartialEq, Debug, Clone)]
pub enum EquationKind {
    Eq,
    Ge,
    Le,
    G,
    L,
    NotEq
}

#[derive(Clone)]
pub struct Summand {
    pub variable_index: u32,
    pub factor: i128,
    pub positive: bool
}



