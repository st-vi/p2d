use std::collections::HashMap;
use std::rc::Rc;

pub struct DDNNF {
    pub root_node: Rc<DDNNFNode>,
    pub number_variables: u32
}

pub struct DDNNFPrinter {
    pub(crate) ddnnf: DDNNF,
    pub(crate) true_sink_id: Option<u32>,
    pub(crate) false_sink_id: Option<u32>,
    pub(crate) current_node_id: u32,
    pub(crate) id_map: HashMap<DDNNFNode, u32>,
    pub edge_counter: u32,
}

impl DDNNFPrinter {
    pub fn print(&mut self) -> String {
        let mut result_string = String::new();
        let root_node = &self.ddnnf.root_node.clone();
        let result = self.print_node(root_node, 0);
        result_string.push_str(&*result);
        result_string.insert_str(0,&format!("nnf {} {} {}\n", self.current_node_id, self.edge_counter, self.ddnnf.number_variables));
        result_string
    }

    fn print_node(&mut self, node: &DDNNFNode, parent_id: u32) -> String {
        let mut result_string = String::new();
        match node {
            DDNNFNode::TrueLeave => {
                if self.true_sink_id.is_none() {
                    let id = self.current_node_id + 1;
                    self.current_node_id = id;
                    self.true_sink_id = Some(id);
                    result_string.push_str(&format!("t {} 0\n", id));
                }
                if parent_id > 0 {
                    result_string.push_str(&format!("{} {} 0\n", parent_id, self.true_sink_id.unwrap()));
                    self.edge_counter += 1;
                }

            }
            DDNNFNode::FalseLeave(_) => {
                if self.false_sink_id.is_none() {
                    let id = self.current_node_id + 1;
                    self.current_node_id = id;
                    self.false_sink_id = Some(id);
                    result_string.push_str(&format!("f {} 0\n", id));
                }
                if parent_id > 0 {
                    result_string.push_str(&format!("{} {} 0\n", parent_id, self.false_sink_id.unwrap()));
                    self.edge_counter += 1;
                }
            }
            DDNNFNode::LiteralLeave(_) => {
                panic!("unreachable code");
            }
            DDNNFNode::AndNode(child_list) => {
                let map_entry = self.id_map.get(node);
                if let Some(existing_id) = map_entry {
                    result_string.push_str(&format!("{} {} 0\n", parent_id, existing_id));
                    self.edge_counter += 1;
                    return result_string;
                }
                let mut literal_children_list: Vec<(u32, bool)> = Vec::new();
                for child_node in &*child_list {
                    if let DDNNFNode::LiteralLeave(ref literal_node) = **child_node {
                        literal_children_list.push((literal_node.index + 1, literal_node.positive))
                    }
                }
                let id = self.current_node_id + 1;
                if literal_children_list.len() != child_list.len() {
                    self.current_node_id = id;
                    result_string.push_str(&format!("a {} 0\n", id));
                    self.id_map.insert(node.clone(), id);
                    for child_node in child_list.iter() {
                        if !matches!(**child_node, DDNNFNode::LiteralLeave(_)){
                            result_string.push_str(&self.print_node(child_node, id));
                        }
                    }
                    if parent_id > 0 {
                        result_string.push_str(&format!("{} {} 0\n", parent_id, id));
                        self.edge_counter += 1;
                    }
                }

                if literal_children_list.len() > 0 {
                    if self.true_sink_id.is_none() {
                        self.true_sink_id = Some(self.current_node_id + 1);
                        self.current_node_id = self.true_sink_id.unwrap();
                        result_string.push_str(&format!("t {} 0\n", id));
                    }
                    result_string.push_str(&format!("{} {} ", if literal_children_list.len() != child_list.len() {id} else {parent_id}, self.true_sink_id.unwrap()));
                    self.edge_counter += 1;
                    for (id,sign) in &literal_children_list {
                        result_string.push_str(&format!("{}{} ", if *sign {""} else {"-"}, *id));
                    }
                    result_string.push_str("0\n");
                }
            }
            DDNNFNode::OrNode(child_list) => {
                let map_entry = self.id_map.get(node);
                if let Some(existing_id) = map_entry {
                    result_string.push_str(&format!("{} {} 0\n", parent_id, existing_id));
                    self.edge_counter += 1;
                    return result_string;
                }
                let mut literal_children_list = Vec::new();
                for child_node in child_list.iter() {
                    if let DDNNFNode::LiteralLeave(ref literal_node) = **child_node {
                        literal_children_list.push((literal_node.index + 1, literal_node.positive))
                    }
                }

                let id = self.current_node_id + 1;
                if literal_children_list.len() != child_list.len() {
                    self.current_node_id = id;
                    result_string.push_str(&format!("o {} 0\n", id));
                    self.id_map.insert(node.clone(), id);
                    for child_node in child_list.iter() {
                        if !matches!(**child_node, DDNNFNode::LiteralLeave(_)){
                            result_string.push_str(&self.print_node(child_node, id));
                        }
                    }
                    if parent_id > 0 {
                        result_string.push_str(&format!("{} {} 0\n", parent_id, id));
                        self.edge_counter += 1;
                    }
                }

                if literal_children_list.len() > 0 {
                    if self.true_sink_id.is_none() {
                        self.true_sink_id = Some(self.current_node_id + 1);
                        self.current_node_id = self.true_sink_id.unwrap();
                        result_string.push_str(&format!("t {} 0\n", id));
                    }
                    result_string.push_str(&format!("{} {} ", if literal_children_list.len() != child_list.len() {id} else {parent_id}, self.true_sink_id.unwrap()));
                    self.edge_counter += 1;
                    for (id,sign) in &literal_children_list {
                        result_string.push_str(&format!("{}{} ", if *sign {""} else {"-"}, *id));
                    }
                    result_string.push_str("0\n");
                }

            }
        }
        result_string
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum DDNNFNode {
    TrueLeave,
    FalseLeave(u32),
    LiteralLeave(Rc<DDNNFLiteral>),
    AndNode(Vec<Rc<DDNNFNode>>),
    OrNode(Vec<Rc<DDNNFNode>>),
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct DDNNFLiteral {
    pub index: u32,
    pub positive: bool
}