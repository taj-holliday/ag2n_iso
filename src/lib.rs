use crate::{dependency_partition::DependencyPartition, nauty::CanonLabeling};
use bimap::BiBTreeMap;
use hashbrown::{HashMap, HashSet};
use itertools::Itertools;
use petgraph::{
    Graph,
    dot::{Config, Dot},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    io::Write,
};

pub mod canon_output;
pub mod dependency;
pub mod dependency_partition;
pub mod nauty;
pub mod utilities;

#[derive(Copy, Clone)]
pub struct NodeData {
    dim: usize,
    vec_count: usize,
    id: usize,
}

impl NodeData {
    fn new(set: &DependencyPartition, id: usize) -> Self {
        Self {
            dim: set.dim(),
            vec_count: set.vec_count(),
            id,
        }
    }
}

impl fmt::Debug for NodeData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:02}-{}D\nID:{:02}", self.vec_count, self.dim, self.id)
    }
}

pub fn complete_graph_gen(dim: usize) {
    let mut id_map = BiBTreeMap::<CanonLabeling, usize>::new();
    let mut map = BTreeMap::<usize, BTreeSet<usize>>::new();

    let first = DependencyPartition::from_dim(0);
    let mut sets = HashSet::<DependencyPartition>::from_iter([first.clone()]);

    let mut id = 0;
    let mut display_map = BTreeMap::<usize, NodeData>::from_iter([(id, NodeData::new(&first, id))]);

    id_map.insert(CanonLabeling::from(&first), id);
    map.insert(id, BTreeSet::new());
    display_map.insert(id, NodeData::new(&first, id));

    id += 1;

    fs::create_dir("caps").unwrap();
    while !sets.is_empty() {
        println!("{} {}", sets.iter().next().unwrap().vec_count(), sets.len());

        for set in &sets {
            let mut file = fs::OpenOptions::new()
                .create(true)
                .write(true)
                .append(true)
                .open(format!("caps/{}dim-{}caps.txt", set.dim(), set.vec_count()))
                .unwrap();

            let _ = writeln!(
                file,
                "{:?}\n\n{:?}\n",
                display_map
                    .get(id_map.get_by_left(&CanonLabeling::from(set)).unwrap())
                    .unwrap(),
                set
            )
            .inspect_err(|err| println!("{err:#?}"));
        }

        sets = sets
            .iter()
            .flat_map(|set| {
                let iter: Box<dyn Iterator<Item = _>> = Box::new(
                    (5..=dim + 1)
                        .step_by(2)
                        .flat_map(|odd| set.add_possible_deps(odd))
                        .filter(|set| set.dep_size_map().get(&4).is_none())
                        .map(move |new_set| (CanonLabeling::from(set), new_set)),
                );

                if set.dim() < dim {
                    Box::new(iter.chain(std::iter::once({
                        let mut clone = set.clone();
                        clone.add_indep_vec();
                        (CanonLabeling::from(set), clone)
                    })))
                } else {
                    iter
                }
            })
            .inspect(|(labeling, new_set)| {
                let set_id = *id_map.get_by_left(labeling).unwrap();
                let new_set_labeling = CanonLabeling::from(new_set);
                let new_set_id = match id_map.get_by_left(&new_set_labeling) {
                    Some(id) => *id,
                    None => {
                        let new_set_id = id;
                        id_map.insert(new_set_labeling, new_set_id);
                        id += 1;
                        new_set_id
                    }
                };

                map.entry(new_set_id).or_default();
                map.entry(set_id)
                    .and_modify(|edges| {
                        edges.insert(new_set_id);
                    })
                    .or_insert(BTreeSet::from_iter([new_set_id]));
                display_map
                    .entry(new_set_id)
                    .or_insert(NodeData::new(new_set, id));
            })
            .map(|(_, set)| set)
            .collect();
    }

    println!("Generating graph!");

    let mut graph = Graph::<NodeData, ()>::new();
    let mut index_map = HashMap::new();
    for id in map.keys() {
        let index = graph.add_node(*display_map.get(id).unwrap());
        index_map.insert(id, index);
    }

    for (canon, edges) in &map {
        for edge in edges {
            graph.add_edge(
                *index_map.get(canon).unwrap(),
                *index_map.get(edge).unwrap(),
                (),
            );
        }
    }

    let mut file = fs::File::create("graph.dot").unwrap();
    write!(
        &mut file,
        "{:?}",
        Dot::with_config(&graph, &[Config::EdgeNoLabel])
    )
    .unwrap();
}

pub fn graph_gen(dim: usize) {
    let mut id_map = BiBTreeMap::<CanonLabeling, usize>::new();
    let mut map = BTreeMap::<usize, BTreeSet<usize>>::new();

    let mut id = 0;

    let mut sets = HashSet::<DependencyPartition>::from_iter([DependencyPartition::from_dim(dim)]);
    while !sets.is_empty() {
        println!("{} {}", sets.iter().next().unwrap().vec_count(), sets.len());

        sets = sets
            .iter()
            .flat_map(|set| {
                (5..=dim + 1)
                    .step_by(2)
                    .flat_map(|odd| set.add_possible_deps(odd))
                    .filter(|set| set.dep_size_map().get(&4).is_none())
                    .map(move |new_set| (CanonLabeling::from(set), new_set))
            })
            .inspect(|(labeling, new_set)| {
                let new_set_labeling = CanonLabeling::from(new_set);
                let new_set_id = match id_map.get_by_left(&new_set_labeling) {
                    Some(id) => *id,
                    None => {
                        let new_set_id = id;
                        id_map.insert(new_set_labeling, new_set_id);
                        id += 1;
                        new_set_id
                    }
                };

                map.entry(new_set_id).or_default();

                let set_id = match id_map.get_by_left(labeling) {
                    Some(id) => *id,
                    None => {
                        let set_id = id;
                        id_map.insert(labeling.clone(), set_id);
                        id += 1;
                        set_id
                    }
                };

                map.entry(set_id)
                    .and_modify(|edges| {
                        edges.insert(new_set_id);
                    })
                    .or_insert(BTreeSet::from_iter([new_set_id]));
            })
            .map(|(_, set)| set)
            .collect();
    }

    println!("Generating graph!");

    let mut graph = Graph::<usize, ()>::new();
    let mut index_map = HashMap::new();
    for id in map.keys() {
        let index = graph.add_node(*id);
        index_map.insert(id, index);
    }

    for (canon, edges) in &map {
        for edge in edges {
            graph.add_edge(
                *index_map.get(canon).unwrap(),
                *index_map.get(edge).unwrap(),
                (),
            );
        }
    }

    let mut file = fs::File::create("graph.dot").unwrap();
    write!(
        &mut file,
        "{:?}",
        Dot::with_config(&graph, &[Config::EdgeNoLabel])
    )
    .unwrap();
}

pub fn generate(dim: usize, mut filter: impl FnMut(&DependencyPartition) -> bool) {
    let mut acc = HashSet::<DependencyPartition>::new();
    let mut sets = HashSet::<DependencyPartition>::from_iter([DependencyPartition::from_dim(dim)]);

    while !sets.is_empty() {
        println!("{} {}", sets.iter().next().unwrap().vec_count(), sets.len());
        acc.extend(sets.clone());

        sets = sets
            .iter()
            .flat_map(|set| {
                (3..=dim + 1)
                    .step_by(2)
                    .flat_map(|odd| set.add_possible_deps(odd))
            })
            .filter(|set| filter(set))
            .collect();
    }

    println!("{} sets", acc.len());
}

pub fn cap_gen(dim: usize) {
    let mut acc = HashSet::<DependencyPartition>::new();
    let mut sets = HashSet::<DependencyPartition>::from_iter([DependencyPartition::from_dim(dim)]);

    while !sets.is_empty() {
        println!("{} {}", sets.iter().next().unwrap().vec_count(), sets.len());
        acc.extend(sets.clone());

        sets = sets
            .iter()
            .flat_map(|set| {
                (5..=dim + 1)
                    .step_by(2)
                    .flat_map(|odd| set.add_possible_deps(odd))
            })
            .filter(|set| set.dep_size_map().get(&4).is_none())
            .collect();
    }

    println!("{} caps", acc.len());
}

pub fn cap_gen_verbose(dim: usize) {
    let mut acc = HashMap::<DependencyPartition, Vec<DependencyPartition>>::from_iter([(
        DependencyPartition::from_dim(dim),
        vec![DependencyPartition::from_dim(dim)],
    )]);
    let mut sets = HashSet::<DependencyPartition>::from_iter([DependencyPartition::from_dim(dim)]);

    while !sets.is_empty() {
        println!("{} {}", sets.iter().next().unwrap().vec_count(), sets.len());

        let new = sets
            .iter()
            .flat_map(|set| {
                (5..=dim + 1)
                    .step_by(2)
                    .flat_map(|odd| set.add_possible_deps(odd))
            })
            .filter(|set| set.dep_size_map().get(&4).is_none())
            .collect_vec();
        for set in &new {
            acc.entry(set.clone())
                .and_modify(|vec| vec.push(set.clone()))
                .or_insert(vec![set.clone()]);
        }

        sets = new.into_iter().collect();
    }

    let mut vec = acc.values().collect_vec();
    vec.sort_by(|v1, v2| v1[0].vec_count().cmp(&v2[0].vec_count()));
    for sets in vec {
        println!("========= EQUIVALENCE CLASS ==========================================\n");
        for set in sets {
            println!("{set:?}\n");
        }
    }

    println!("{} caps", acc.len());
}
