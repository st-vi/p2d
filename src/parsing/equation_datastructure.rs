use bimap::{BiHashMap, BiMap};

pub struct OPBFile {
    pub name_map: BiMap<String, u32>,
    pub equations: Vec<Equation>,
    pub max_name_index: u32
}

impl OPBFile {
    pub fn new() -> OPBFile {
        OPBFile {
            name_map: BiHashMap::new(),
            equations: Vec::new(),
            max_name_index: 0
        }
    }
}
#[derive(Clone)]
pub struct Equation {
    pub lhs: Vec<Summand>,
    pub rhs: i32,
    pub kind: EquationKind
}

#[derive(PartialEq, Debug, Clone)]
pub enum EquationKind {
    Eq,
    Ge,
    Le
}

#[derive(Clone)]
pub struct Summand {
    pub variable_index: u32,
    pub factor: i32,
    pub positive: bool
}



