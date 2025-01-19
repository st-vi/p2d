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
    pub(crate) id_map: HashMap<u32, u32>,
    pub edge_counter: u32,
    pub(crate) node_counter: u32
}

impl DDNNFPrinter {
    pub fn print(&mut self) -> String {
        let mut result_string = String::new();
        let root_node = &self.ddnnf.root_node.clone();
        if let DDNNFNode::FalseLeave = **root_node {
            //result_string.push_str(&format!("nnf {} {} {}\n", 2, 1, self.ddnnf.number_variables));
            self.node_counter += 2;
            result_string.push_str("o 1 0\n");
            result_string.push_str("f 2 0\n");
            result_string.push_str("1 2 1 0\n");
        }else{
            let empty_vec: Vec<(u32, bool)> = Vec::new();
            let result = self.print_node(root_node, 0, empty_vec);
            result_string.push_str(&*result);
            //result_string.insert_str(0,&format!("nnf {} {} {}\n", self.current_node_id, self.edge_counter, self.ddnnf.number_variables));
        }
        println!("number_nodes: {}", self.node_counter);
        result_string
    }

    fn print_node(&mut self, node: &DDNNFNode, parent_id: u32, implied_literals: Vec<(u32, bool)>) -> String {
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
                    self.node_counter += 1;
                }

            }
            DDNNFNode::FalseLeave => {
                if self.false_sink_id.is_none() {
                    let id = self.current_node_id + 1;
                    self.current_node_id = id;
                    self.false_sink_id = Some(id);
                    result_string.push_str(&format!("f {} 0\n", id));
                    self.node_counter += 1;
                }
                if parent_id > 0 {
                    result_string.push_str(&format!("{} {} 0\n", parent_id, self.false_sink_id.unwrap()));
                    self.edge_counter += 1;
                    self.node_counter += 1;
                }
            }
            DDNNFNode::LiteralLeave(_) => {
                panic!("unreachable code");
            }
            DDNNFNode::AndNode(child_list,node_id) => {
                let map_entry = self.id_map.get(node_id);
                if let Some(existing_id) = map_entry {
                    result_string.push_str(&format!("{} {} ", parent_id, existing_id));
                    for (id, sign) in implied_literals {
                        result_string.push_str(&format!("{}{} ",if sign {""} else {"-"}, id));
                    }
                    result_string.push_str(&format!("0\n"));
                    self.edge_counter += 1;
                    return result_string;
                }
                let mut non_literal_children_counter = 0;
                let mut local_implied_literals: Vec<(u32, bool)> = Vec::new();
                for child_node in &*child_list {
                    if let DDNNFNode::LiteralLeave(ref literal_node) = **child_node {
                        local_implied_literals.push((literal_node.index + 1, literal_node.positive))
                    }else{
                        non_literal_children_counter += 1;
                    }
                }
                if non_literal_children_counter == 0 {
                    if self.true_sink_id.is_none() {
                        self.true_sink_id = Some(self.current_node_id + 1);
                        self.current_node_id = self.true_sink_id.unwrap();
                        result_string.push_str(&format!("t {} 0\n", self.true_sink_id.unwrap()));
                        self.node_counter += 1;
                    }
                    if parent_id == 0 {
                        let id = self.current_node_id + 1;
                        self.current_node_id = id;
                        self.id_map.insert(*node_id, id);
                        result_string.push_str(&format!("a {} 0\n", id));
                        result_string.push_str(&format!("{} {} ", id, self.true_sink_id.unwrap()));
                    }else{
                        result_string.push_str(&format!("{} {} ", parent_id, self.true_sink_id.unwrap()));
                    }
                    for (id, sign) in local_implied_literals {
                        result_string.push_str(&format!("{}{} ",if sign {""} else {"-"}, id));
                    }
                    for (id, sign) in implied_literals {
                        result_string.push_str(&format!("{}{} ",if sign {""} else {"-"}, id));
                    }
                    result_string.push_str(&format!("0\n"));
                }else if non_literal_children_counter == 1 {
                    for child_node in child_list {
                        if !matches!(**child_node, DDNNFNode::LiteralLeave(_)){
                            let mut combined = implied_literals.clone();
                            combined.extend(local_implied_literals.iter());
                            result_string.push_str(&self.print_node(child_node, parent_id, combined));
                        }
                    }
                }else {
                    let id = self.current_node_id + 1;
                    self.current_node_id = id;
                    self.id_map.insert(*node_id, id);
                    result_string.push_str(&format!("a {} 0\n", id));
                    if parent_id != 0 {
                        result_string.push_str(&format!("{} {} ", parent_id, id));
                        for (id, sign) in &implied_literals {
                            result_string.push_str(&format!("{}{} ",if *sign {""} else {"-"}, *id));
                        }
                        result_string.push_str(&format!("0\n"));
                    }

                    for child_node in child_list {
                        if !matches!(**child_node, DDNNFNode::LiteralLeave(_)){
                            result_string.push_str(&self.print_node(child_node, id, local_implied_literals.clone()));
                        }
                    }
                }

                /*
                let map_entry = self.id_map.get(node_id);
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
                    self.node_counter += 1;
                    self.id_map.insert(*node_id, id);
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
                if literal_children_list.len() + 1 == child_list.len() {
                    for child_node in child_list.iter() {
                        if !matches!(**child_node, DDNNFNode::LiteralLeave(_)){
                            result_string.push_str(&self.print_node(child_node, id));
                        }
                    }
                    if parent_id > 0 {
                        result_string.push_str(&format!("{} {} ", parent_id, id));
                        for (id,sign) in &literal_children_list {
                            self.node_counter += 1;
                            result_string.push_str(&format!("{}{} ", if *sign {""} else {"-"}, *id));
                        }
                        self.edge_counter += 1;
                        result_string.push_str(&format!("0\n"));
                    }
                }else if literal_children_list.len() > 0 {
                    if self.true_sink_id.is_none() {
                        self.true_sink_id = Some(self.current_node_id + 1);
                        self.current_node_id = self.true_sink_id.unwrap();
                        result_string.push_str(&format!("t {} 0\n", self.true_sink_id.unwrap()));
                        self.node_counter += 1;
                    }
                    result_string.push_str(&format!("{} {} ", if literal_children_list.len() != child_list.len() {id} else {parent_id}, self.true_sink_id.unwrap()));
                    self.edge_counter += 1;
                    for (id,sign) in &literal_children_list {
                        self.node_counter += 1;
                        result_string.push_str(&format!("{}{} ", if *sign {""} else {"-"}, *id));
                    }
                    result_string.push_str("0\n");
                }

                 */
            }
            DDNNFNode::OrNode(child_list,node_id) => {
                //TODO handle single child
                let map_entry = self.id_map.get(node_id);
                if let Some(existing_id) = map_entry {
                    result_string.push_str(&format!("{} {} ", parent_id, existing_id));
                    for (id, sign) in implied_literals {
                        result_string.push_str(&format!("{}{} ",if sign {""} else {"-"}, id));
                    }
                    result_string.push_str(&format!("0\n"));
                    self.edge_counter += 1;
                    return result_string;
                }
                let id = self.current_node_id + 1;
                self.current_node_id = id;
                self.id_map.insert(*node_id, id);
                result_string.push_str(&format!("o {} 0\n", id));
                let mut local_implied_literals: Vec<(u32, bool)> = Vec::new();
                if parent_id != 0 {
                    result_string.push_str(&format!("{} {} ", parent_id, id));
                    for (id, sign) in &implied_literals {
                        result_string.push_str(&format!("{}{} ",if *sign {""} else {"-"}, *id));
                    }
                    result_string.push_str(&format!("0\n"));

                }else{
                    local_implied_literals = implied_literals.clone();
                }

                for child_node in &*child_list {
                    if let DDNNFNode::LiteralLeave(ref literal_node) = **child_node {
                        if self.true_sink_id.is_none() {
                            self.true_sink_id = Some(self.current_node_id + 1);
                            self.current_node_id = self.true_sink_id.unwrap();
                            result_string.push_str(&format!("t {} 0\n", self.true_sink_id.unwrap()));
                            self.node_counter += 1;
                        }
                        result_string.push_str(&format!("{} {} ", id, self.true_sink_id.unwrap()));
                        result_string.push_str(&format!("{}{} ", if literal_node.positive {""} else {"-"}, literal_node.index + 1));
                        for (index, positive) in &local_implied_literals {
                            result_string.push_str(&format!("{}{} ", if *positive {""} else {"-"}, *index));
                        }
                        result_string.push_str(&format!("0\n"));
                    }else{
                        result_string.push_str(&self.print_node(child_node, id, local_implied_literals.clone()));
                    }
                }
                /*
                let map_entry = self.id_map.get(node_id);
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
                    self.node_counter += 1;
                    self.id_map.insert(*node_id, id);
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
                        self.node_counter += 1;
                    }
                    result_string.push_str(&format!("{} {} ", if literal_children_list.len() != child_list.len() {id} else {parent_id}, self.true_sink_id.unwrap()));
                    self.edge_counter += 1;
                    for (id,sign) in &literal_children_list {
                        result_string.push_str(&format!("{}{} ", if *sign {""} else {"-"}, *id));
                        self.node_counter += 1;
                    }
                    result_string.push_str("0\n");
                }

                 */

            }
        }
        result_string
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum DDNNFNode {
    TrueLeave,
    FalseLeave,
    LiteralLeave(Rc<DDNNFLiteral>),
    AndNode(Vec<Rc<DDNNFNode>>, u32),
    OrNode(Vec<Rc<DDNNFNode>>, u32),
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct DDNNFLiteral {
    pub index: u32,
    pub positive: bool
}