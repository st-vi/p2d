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


fn test() {
    let mut hasher = DefaultHasher::new();
    /*
    let mut formula = PseudoBooleanFormula{
        constraints: Vec::new(),
        number_variables: 2,
        constraints_by_variable: Vec::new(),
    };

    let mut c = Constraint{
        unassigned_literals: HashSet::new(),
        sum_true: 0,
        sum_unassigned: 2,
        factor_sum: 2,
        degree: 2,
        assignments: vec![None,None],
        literals: vec![Some(Literal{ positive: true, index: 0, factor: 1}), Some(Literal{ positive: true, index: 1, factor: 1})],
    };
    c.unassigned_literals.insert(Literal{ positive: true, index: 0, factor: 1});
    c.unassigned_literals.insert(Literal{ positive: true, index: 1, factor: 1});
    formula.constraints.push(c);

    let mut s1 = DefaultHasher::new();

    for c in &formula.constraints {
        if c.is_unsatisfied() {
            c.hash(&mut s1);
        }
    }

    let h1 = s1.finish();

    formula.constraints.get_mut(0).unwrap().sum_true = 1;
    formula.constraints.get_mut(0).unwrap().sum_unassigned = 1;
    formula.constraints.get_mut(0).unwrap().unassigned_literals.remove(&Literal{ positive: true, index: 0, factor: 1});
    formula.constraints.get_mut(0).unwrap().assignments[0] = Some(true);
    let mut s2 = DefaultHasher::new();

    for c in &formula.constraints {
        if c.is_unsatisfied() {
            c.hash(&mut s2);
        }
    }

    let h2 = s2.finish();*/
    None::<u32>.hash(&mut hasher);
    None::<u32>.hash(&mut hasher);
    let h1 = hasher.finish();
    hasher = DefaultHasher::new();
    None::<u32>.hash(&mut hasher);
    Some::<u32>(1).hash(&mut hasher);
    let h2 = hasher.finish();

    println!("{}", h1 == h2);
}

fn main() {
    //test();

    let file_content = fs::read_to_string("./test_models/berkeleydb.opb").expect("cannot read file");
    let opb_file = parsing::parser::parse(file_content.as_str()).expect("error while parsing");
    let formula = PseudoBooleanFormula::new(&opb_file);
    let mut solver = Solver::new(formula);
    let model_count = solver.solve();
    println!("result: {}", model_count);
    println!("{:#?}", solver.statistics);


}
