use crate::{
    dependency::{Dependency, DependencySet},
    dependency_partition::DependencyPartition,
    nauty::CanonLabeling,
};
use itertools::Itertools;
use nauty_Traces_sys::{SETWORDSNEEDED, WORDSIZE};
use std::{collections::BTreeMap, fmt};

pub struct CanonPartition {
    cells: BTreeMap<DependencySet, usize>,
}

impl From<&DependencyPartition> for CanonPartition {
    fn from(value: &DependencyPartition) -> Self {
        let dep_count =
            value.spanning_dep_counts().iter().count() + value.comb_dep_counts().iter().count();
        let labeling = CanonLabeling::from(value);

        let mut dep_map = BTreeMap::new();

        for vec_i in (dep_count..labeling.vertex_count).map(|i| i * labeling.set_word_count) {
            let mut deps = DependencySet::empty();

            for num_i in 0..SETWORDSNEEDED(dep_count) {
                for bit_i in 0..WORDSIZE as usize {
                    if (labeling.graph[vec_i + num_i] >> (WORDSIZE as usize - 1 - bit_i)) & 1 == 1 {
                        deps.insert(Dependency::from(num_i * WORDSIZE as usize + bit_i));
                    }
                }
            }

            dep_map
                .entry(deps)
                .and_modify(|count| *count += 1)
                .or_insert(1);
        }

        Self { cells: dep_map }
    }
}

impl fmt::Debug for CanonPartition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut deps = self
            .cells
            .keys()
            .flat_map(|cell| cell.into_iter())
            .unique()
            .collect_vec();
        deps.sort();

        for dep in deps {
            for (cell, count) in &self.cells {
                if cell.contains(&dep) {
                    for _ in 0..*count {
                        write!(f, "| __ ")?;
                    }
                } else {
                    for _ in 0..*count {
                        write!(f, "|    ")?;
                    }
                }
            }
            writeln!(f, "| {dep:?}")?;
        }

        for i in 0..self.cells.values().sum() {
            write!(f, "| ")?;
            if i < 10 {
                write!(f, "0")?;
            }
            write!(f, "{i} ")?;
        }
        write!(f, "|")
    }
}
