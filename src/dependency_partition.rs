use crate::{
    dependency::{Dependency, DependencyCell, DependencySet},
    nauty::{self, CanonLabeling, OPTIONS},
    utilities::RestrictedPartitionIterator,
};
use hashbrown::HashMap;
use itertools::Itertools;
use nauty_Traces_sys::{ADDONEEDGE, SETWORDSNEEDED, empty_graph};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
};

#[derive(Clone)]
pub struct DependencyPartition {
    cells: BTreeMap<DependencyCell, (usize, BTreeSet<DependencySet>)>,
    spanning_dep_counts: HashMap<Dependency, usize>,
    comb_dep_counts: HashMap<DependencySet, usize>,
}

impl DependencyPartition {
    pub fn from_dim(dim: usize) -> Self {
        Self {
            cells: BTreeMap::from_iter([(DependencyCell::new(true), (dim + 1, BTreeSet::new()))]),
            spanning_dep_counts: HashMap::new(),
            comb_dep_counts: HashMap::new(),
        }
    }

    pub fn extended_type(&self) -> String {
        let mut out = String::new();
        let mut deps = vec![];

        let alphabet = "abcdefghijklmnopqrstuvwxyz";
        for (i, (dep, count)) in self.spanning_dep_counts.iter().enumerate() {
            let label = alphabet.chars().nth(i).unwrap();

            out.push(label);
            out.push_str(&(count - 1).to_string());
            out.push('-');

            deps.push((label, dep));
        }

        if deps.len() > 1 {
            out.push('(');

            for comb in (2..=deps.len()).flat_map(|len| deps.iter().combinations(len)) {
                let mut count = 0;

                for (label, _) in &comb {
                    out.push(*label);
                }

                for (cell, (cell_count, _)) in &self.cells {
                    let mut pass = true;
                    for (_, dep) in &comb {
                        if !cell.spanning_deps.contains(dep) {
                            pass = false;
                            break;
                        }
                    }

                    if pass {
                        count += cell_count;
                    }
                }

                out.push_str(&count.to_string());
                out.push('-');
            }

            out.pop();
            out.push(')');
        } else {
            out.pop();
        }

        out
    }

    pub fn dep_size_map(&self) -> HashMap<usize, usize> {
        let mut map = HashMap::new();

        for size in self
            .spanning_dep_counts
            .values()
            .chain(self.comb_dep_counts.values())
        {
            map.entry(*size)
                .and_modify(|size_count| *size_count += 1)
                .or_insert(1);
        }

        map
    }

    pub fn vec_count(&self) -> usize {
        self.basis_len() + self.spanning_dep_counts.iter().count()
    }

    pub fn basis_len(&self) -> usize {
        self.cells
            .iter()
            .filter_map(|(cell, (count, _))| cell.is_basis.then_some(count))
            .sum::<usize>()
    }

    pub fn dim(&self) -> usize {
        self.basis_len() - 1
    }

    pub fn spanning_dep_counts(&self) -> &HashMap<Dependency, usize> {
        &self.spanning_dep_counts
    }

    pub fn comb_dep_counts(&self) -> &HashMap<DependencySet, usize> {
        &self.comb_dep_counts
    }

    pub fn add_indep_vec(&mut self) {
        let cell = DependencyCell::new(true);
        self.cells
            .entry(cell)
            .and_modify(|(count, _)| *count += 1)
            .or_insert((1, BTreeSet::new()));
    }

    pub fn add_possible_deps(&self, size: usize) -> impl Iterator<Item = Self> {
        self.possible_deps(size).map(move |dep| {
            let mut clone = self.clone();
            clone.add_dep(dep);
            clone
        })
    }

    pub fn possible_deps(
        &self,
        size: usize,
    ) -> impl Iterator<Item = BTreeSet<(&DependencyCell, usize)>> {
        // All possible dependencies can be expressed as a sum of basis elements
        let basis = self
            .cells
            .iter()
            .filter(|(cell, _)| cell.is_basis)
            .collect_vec();

        // Take all partitions of elements among the dependency cells of the basis
        RestrictedPartitionIterator::new(
            basis.iter().map(|(_, (count, _))| *count).collect_vec(),
            size,
        )
        .map(move |partition| {
            BTreeSet::from_iter(
                partition
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, count)| (count > 0).then_some((basis[i].0, count))),
            )
        })
        // Filter out dependencies which create a duplicate vector
        .filter(|dep| {
            // Spanning deps
            for other_dep in self.spanning_dep_counts.keys() {
                let diff = self
                    .cells
                    .iter()
                    .filter_map(|(cell, (count, _))| {
                        if let Some((_, dep_count)) =
                            dep.iter().find(|(dep_cell, _)| *dep_cell == cell)
                        {
                            Some(if cell.spanning_deps.contains(other_dep) {
                                count - dep_count
                            } else {
                                *count
                            })
                        } else {
                            cell.spanning_deps.contains(other_dep).then_some(*count)
                        }
                    })
                    .sum::<usize>();

                if diff + 1 == 2 {
                    return false;
                }
            }

            // Comb deps
            for other_dep in self.comb_dep_counts.keys() {
                let diff = self
                    .cells
                    .iter()
                    .filter_map(|(cell, (count, comb_deps))| {
                        if let Some((_, dep_count)) =
                            dep.iter().find(|(dep_cell, _)| *dep_cell == cell)
                        {
                            Some(if comb_deps.contains(other_dep) {
                                count - dep_count
                            } else {
                                *count
                            })
                        } else {
                            comb_deps.contains(other_dep).then_some(*count)
                        }
                    })
                    .sum::<usize>();

                if diff + 1 == 2 {
                    return false;
                }
            }

            true
        })
    }

    pub fn add_dep(&mut self, dep: BTreeSet<(&DependencyCell, usize)>) {
        // The dependency cannot have any redundant cells
        assert!(!dep.iter().any(|(_, count)| *count == 0));

        // Add dependency

        let dep_marker = Dependency::from(
            self.spanning_dep_counts
                .keys()
                .map(|marker| marker.id)
                .max()
                .unwrap_or(0)
                + 1,
        );

        // Split cells
        for (cell, dep_count) in &dep {
            let (count, comb_deps) = self.cells.get_mut(cell).unwrap();
            let comb_deps = comb_deps.clone();
            *count = count.checked_sub(*dep_count).unwrap();

            if *count == 0 {
                self.cells.remove(cell);
            }

            let mut new_cell = (*cell).clone();
            new_cell.spanning_deps.insert(dep_marker);
            self.cells.insert(new_cell, (*dep_count, comb_deps));
        }

        // Add final cell
        self.cells.insert(
            DependencyCell {
                spanning_deps: DependencySet::from_iter([dep_marker]),
                is_basis: false,
            },
            (1, BTreeSet::new()),
        );

        // Update spanning dependency counts
        self.spanning_dep_counts.insert(
            dep_marker,
            dep.iter().map(|(_, count)| count).sum::<usize>() + 1,
        );

        // Add implied dependencies

        let mut delta = HashMap::<DependencyCell, BTreeSet<DependencySet>>::new();
        let mut dep_count_delta = HashMap::new();

        // Sum of this dep + spanning deps
        for spanning_dep in self
            .spanning_dep_counts
            .keys()
            .filter(|spanning_dep| **spanning_dep != dep_marker)
        {
            let new_comb_dep = DependencySet::from_iter([dep_marker, *spanning_dep]);

            let add_list = self.cells.iter().filter(|(cell, _)| {
                cell.spanning_deps.contains(spanning_dep) ^ cell.spanning_deps.contains(&dep_marker)
            });

            let mut dep_count = 0;
            for (cell, (count, _)) in add_list {
                if let Some(deps) = delta.get_mut(cell) {
                    deps.insert(new_comb_dep);
                } else {
                    delta.insert(cell.clone(), BTreeSet::from_iter([new_comb_dep]));
                }
                dep_count += count;
            }

            dep_count_delta.insert(new_comb_dep, dep_count);
        }

        // Sum of this dep + other comb deps
        for comb_dep in self.comb_dep_counts.keys() {
            let new_comb_dep = comb_dep.copy_with(dep_marker);

            let add_list = self.cells.iter().filter(|(cell, (_, comb_deps))| {
                comb_deps.contains(comb_dep) ^ cell.spanning_deps.contains(&dep_marker)
            });

            let mut dep_count = 0;
            for (cell, (count, _)) in add_list {
                if let Some(deps) = delta.get_mut(cell) {
                    deps.insert(new_comb_dep);
                } else {
                    delta.insert(cell.clone(), BTreeSet::from_iter([new_comb_dep]));
                }
                dep_count += count;
            }

            dep_count_delta.insert(new_comb_dep, dep_count);
        }

        // Insert comb deps
        for (cell, mut new_comb_deps) in delta {
            let (_, comb_deps) = self.cells.get_mut(&cell).unwrap();
            comb_deps.append(&mut new_comb_deps);
        }

        // Update comb dependency counts
        self.comb_dep_counts.extend(dep_count_delta);
    }
}

impl Hash for DependencyPartition {
    fn hash<H: Hasher>(&self, state: &mut H) {
        CanonLabeling::from(self).hash(state);
    }
}

impl PartialEq for DependencyPartition {
    fn eq(&self, other: &Self) -> bool {
        CanonLabeling::from(self) == CanonLabeling::from(other)
    }
}

impl Eq for DependencyPartition {}

impl From<&DependencyPartition> for CanonLabeling {
    fn from(value: &DependencyPartition) -> Self {
        nauty::DenseGraph::from(value).into_canon_labeling(&mut OPTIONS.clone())
    }
}

impl From<&DependencyPartition> for nauty::DenseGraph {
    fn from(value: &DependencyPartition) -> Self {
        let spanning_dep_count = value.spanning_dep_counts.iter().count();
        let comb_dep_count = value.comb_dep_counts.iter().count();

        let vertex_count = value.cells.values().map(|(count, _)| count).sum::<usize>()
            + spanning_dep_count
            + value.comb_dep_counts.iter().count();
        let set_word_count = SETWORDSNEEDED(vertex_count);
        let mut graph = empty_graph(set_word_count, vertex_count);

        let spanning_dep_indices = HashMap::<Dependency, usize>::from_iter(
            value
                .spanning_dep_counts
                .keys()
                .enumerate()
                .map(|(i, spanning_dep)| (*spanning_dep, i)),
        );

        let comb_dep_indices = HashMap::<&DependencySet, usize>::from_iter(
            value
                .comb_dep_counts
                .keys()
                .enumerate()
                .map(|(i, comb_dep)| (comb_dep, i + spanning_dep_count)),
        );

        let mut cell_i = spanning_dep_count + comb_dep_count;
        for (cell, (count, comb_deps)) in &value.cells {
            for vec_i in 0..*count {
                for spanning_dep in cell.spanning_deps.into_iter() {
                    ADDONEEDGE(
                        &mut graph,
                        cell_i + vec_i,
                        *spanning_dep_indices.get(&spanning_dep).unwrap(),
                        set_word_count,
                    );
                }

                for comb_dep in comb_deps {
                    ADDONEEDGE(
                        &mut graph,
                        cell_i + vec_i,
                        *comb_dep_indices.get(comb_dep).unwrap(),
                        set_word_count,
                    );
                }
            }

            cell_i += count;
        }

        let partition = nauty::Partition::from_indices(&[
            spanning_dep_indices
                .values()
                .chain(comb_dep_indices.values())
                .copied()
                .collect_vec(),
            ((spanning_dep_count + comb_dep_count)..cell_i).collect_vec(),
        ]);

        nauty::DenseGraph {
            graph,
            partition,
            set_word_count,
            vertex_count,
        }
    }
}

impl Debug for DependencyPartition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let mut cells = self.cells.iter().collect_vec();
        cells.sort_by(|(b1, _), (b2, _)| {
            let ord = b2.is_basis.cmp(&b1.is_basis);
            if ord == Ordering::Equal {
                let mut deps = b1
                    .spanning_deps
                    .into_iter()
                    .chain(b2.spanning_deps.into_iter())
                    .unique()
                    .collect_vec();
                deps.sort();

                for dep in deps {
                    let ord = b2
                        .spanning_deps
                        .contains(&dep)
                        .cmp(&b1.spanning_deps.contains(&dep));

                    if ord != Ordering::Equal {
                        return ord;
                    }
                }

                Ordering::Equal
            } else {
                ord
            }
        });

        let mut spanning_dep_counts = self.spanning_dep_counts.iter().collect_vec();
        spanning_dep_counts.sort();

        for (dep, _) in &spanning_dep_counts {
            for (cell, (count, _)) in &cells {
                if cell.spanning_deps.contains(dep) {
                    for _ in 0..*count {
                        write!(f, "▏▂▂ ")?;
                    }
                } else {
                    for _ in 0..*count {
                        write!(f, "▏   ")?;
                    }
                }
            }
            writeln!(f, "▏{}", dep.id)?;
        }

        /*let mut comb_dep_counts = self.comb_dep_counts.keys().collect_vec();
        comb_dep_counts.sort_by(|comb1, comb2| {
            let vec1 = comb1.into_iter().collect_vec();
            let vec2 = comb2.into_iter().collect_vec();

            let ordering = vec1.len().cmp(&vec2.len());
            if ordering != Ordering::Equal {
                return ordering;
            }

            let mut combined = vec1.iter().chain(vec2.iter()).unique().collect_vec();
            combined.sort();

            for dep in combined {
                let ordering = vec2.contains(dep).cmp(&vec1.contains(dep));
                if ordering != Ordering::Equal {
                    return ordering;
                }
            }

            Ordering::Equal
        });

        for dep in comb_dep_counts {
            for (_, (count, comb_deps)) in &cells {
                if comb_deps.contains(dep) {
                    for _ in 0..*count {
                        write!(f, "▏▂▂ ")?;
                    }
                } else {
                    for _ in 0..*count {
                        write!(f, "▏   ")?;
                    }
                }
            }

            write!(f, "▏")?;

            let mut ids = dep.into_iter().map(|dep| dep.id).collect_vec();
            ids.sort();

            write!(f, "{}", ids[0])?;
            for id in ids.iter().skip(1) {
                write!(f, " + {id}")?;
            }
            writeln!(f)?;
        }*/

        for (cell, (count, _)) in &cells {
            for _ in 0..*count {
                if cell.is_basis {
                    write!(f, "▏BA ")?;
                } else {
                    write!(f, "▏   ")?;
                }
            }
        }
        writeln!(f, "▏")?;

        for i in 0..cells.iter().map(|(_, (count, _))| *count).sum() {
            write!(f, "▏")?;
            if i < 10 {
                write!(f, "0")?;
            }
            write!(f, "{i} ")?;
        }
        write!(f, "▏")
    }
}

/* alternate version with extended type
impl Debug for DependencyPartition {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let mut cells = self.cells.iter().collect_vec();
        cells.sort_by(|(b1, _), (b2, _)| {
            let ord = b2.is_basis.cmp(&b1.is_basis);
            if ord == Ordering::Equal {
                let mut deps = b1
                    .spanning_deps
                    .into_iter()
                    .chain(b2.spanning_deps.into_iter())
                    .unique()
                    .collect_vec();
                deps.sort();

                for dep in deps {
                    let ord = b2
                        .spanning_deps
                        .contains(&dep)
                        .cmp(&b1.spanning_deps.contains(&dep));

                    if ord != Ordering::Equal {
                        return ord;
                    }
                }

                Ordering::Equal
            } else {
                ord
            }
        });

        let mut spanning_dep_counts = self.spanning_dep_counts.iter().collect_vec();
        spanning_dep_counts.sort();

        //

        let mut format = String::new();
        let mut out = String::new();
        let mut deps = vec![];

        let alphabet = "abcdefghijklmnopqrstuvwxyz";
        for (dep, count) in &spanning_dep_counts {
            let label = alphabet.chars().nth(dep.id).unwrap();

            format.push(label);
            out.push_str(&(*count - 1).to_string());

            format.push('-');
            out.push('-');

            deps.push((label, dep));
        }

        if deps.len() > 1 {
            format.push('(');
            out.push('(');

            for comb in (2..=deps.len()).flat_map(|len| deps.iter().combinations(len)) {
                let mut count = 0;

                for (label, _) in &comb {
                    format.push(*label);
                }

                for (cell, (cell_count, _)) in &self.cells {
                    let mut pass = true;
                    for (_, dep) in &comb {
                        if !cell.spanning_deps.contains(dep) {
                            pass = false;
                            break;
                        }
                    }

                    if pass {
                        count += cell_count;
                    }
                }

                out.push_str(&count.to_string());

                format.push('-');
                out.push('-');
            }

            format.pop();
            out.pop();

            format.push(')');
            out.push(')');
        } else {
            format.pop();
            out.pop();
        }

        writeln!(f, "{format}\n{out}")?;

        //

        for (dep, _) in &spanning_dep_counts {
            for (cell, (count, _)) in &cells {
                if cell.spanning_deps.contains(dep) {
                    for _ in 0..*count {
                        write!(f, "▏▂▂ ")?;
                    }
                } else {
                    for _ in 0..*count {
                        write!(f, "▏   ")?;
                    }
                }
            }
            writeln!(f, "▏{}", alphabet.chars().nth(dep.id).unwrap())?;
        }

        /*
        let mut comb_dep_counts = self.comb_dep_counts.keys().collect_vec();
        comb_dep_counts.sort_by(|comb1, comb2| {
            let vec1 = comb1.into_iter().collect_vec();
            let vec2 = comb2.into_iter().collect_vec();

            let ordering = vec1.len().cmp(&vec2.len());
            if ordering != Ordering::Equal {
                return ordering;
            }

            let mut combined = vec1.iter().chain(vec2.iter()).unique().collect_vec();
            combined.sort();

            for dep in combined {
                let ordering = vec2.contains(dep).cmp(&vec1.contains(dep));
                if ordering != Ordering::Equal {
                    return ordering;
                }
            }

            Ordering::Equal
        });

        for dep in comb_dep_counts {
            for (_, (count, comb_deps)) in &cells {
                if comb_deps.contains(dep) {
                    for _ in 0..*count {
                        write!(f, "▏▂▂ ")?;
                    }
                } else {
                    for _ in 0..*count {
                        write!(f, "▏   ")?;
                    }
                }
            }

            write!(f, "▏")?;

            let mut ids = dep.into_iter().map(|dep| dep.id).collect_vec();
            ids.sort();

            write!(f, "{}", alphabet.chars().nth(ids[0]).unwrap())?;
            for id in ids.iter().skip(1) {
                write!(f, " + {}", alphabet.chars().nth(*id).unwrap())?;
            }
            writeln!(f)?;
        }*/

        for (cell, (count, _)) in &cells {
            for _ in 0..*count {
                if cell.is_basis {
                    write!(f, "▏BA ")?;
                } else {
                    write!(f, "▏   ")?;
                }
            }
        }
        writeln!(f, "▏")?;

        for i in 0..cells.iter().map(|(_, (count, _))| *count).sum() {
            write!(f, "▏")?;
            if i < 10 {
                write!(f, "0")?;
            }
            write!(f, "{i} ")?;
        }
        write!(f, "▏")
    }
}
*/

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nauty::Partition;
    use core::iter::Iterator;

    #[test]
    fn spanning_dependency_set() {
        let set = DependencySet::from_iter([
            Dependency::from(1),
            Dependency::from(5),
            Dependency::from(7),
            Dependency::from(25),
        ]);

        assert_eq!(
            set.deps,
            0b00000000_00000000_00000000_00000000_00000010_00000000_00000000_10100010
        );

        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(1.into()));
        assert_eq!(iter.next(), Some(5.into()));
        assert_eq!(iter.next(), Some(7.into()));
        assert_eq!(iter.next(), Some(25.into()));
    }

    #[test]
    fn cell_rep_new() {
        for n in 0..10 {
            let cell_rep = DependencyPartition::from_dim(n);
            assert_eq!(
                cell_rep,
                DependencyPartition {
                    cells: BTreeMap::from_iter([(
                        DependencyCell::new(true),
                        (n + 1, BTreeSet::new())
                    )]),
                    spanning_dep_counts: HashMap::new(),
                    comb_dep_counts: HashMap::new(),
                }
            );
        }
    }

    #[test]
    fn cell_rep_add_dependency() {
        let mut cell_rep = DependencyPartition::from_dim(5);
        cell_rep.add_dep(BTreeSet::from_iter([(&DependencyCell::new(true), 3)]));

        // |__|__|__|  |  |  |__|
        // |1 |2 |3 |4 |5 |6 |7 |
        // | basis           | not basis

        assert_eq!(
            cell_rep.cells,
            BTreeMap::from_iter([
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                        is_basis: false,
                    },
                    (1, BTreeSet::new()),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                        is_basis: true,
                    },
                    (3, BTreeSet::new()),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::empty(),
                        is_basis: true,
                    },
                    (3, BTreeSet::new()),
                ),
            ])
        );

        assert_eq!(
            cell_rep.spanning_dep_counts,
            HashMap::from_iter([(Dependency::from(1), 4)])
        );

        assert_eq!(cell_rep.comb_dep_counts, HashMap::new());

        // spanning:
        // |__|__|__|  |  |  |__|  |: 1
        // |__|__|  |__|  |  |  |__|: 2
        // comb:
        // |  |  |__|__|  |  |__|__|: 1 + 2
        // |1 |2 |3 |4 |5 |6 |7 |8 |
        // | basis           | not basis

        cell_rep.add_dep(BTreeSet::from_iter([
            (
                &DependencyCell {
                    spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                    is_basis: true,
                },
                2,
            ),
            (
                &DependencyCell {
                    spanning_deps: DependencySet::empty(),
                    is_basis: true,
                },
                1,
            ),
        ]));

        assert_eq!(
            cell_rep.cells,
            BTreeMap::from_iter([
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                        is_basis: false,
                    },
                    (
                        1,
                        BTreeSet::from_iter([DependencySet::from_iter([
                            Dependency::from(1),
                            Dependency::from(2)
                        ])])
                    ),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(2)]),
                        is_basis: false,
                    },
                    (
                        1,
                        BTreeSet::from_iter([DependencySet::from_iter([
                            Dependency::from(1),
                            Dependency::from(2)
                        ])])
                    ),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                        is_basis: true,
                    },
                    (
                        1,
                        BTreeSet::from_iter([DependencySet::from_iter([
                            Dependency::from(1),
                            Dependency::from(2)
                        ])])
                    ),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(2)]),
                        is_basis: true,
                    },
                    (
                        1,
                        BTreeSet::from_iter([DependencySet::from_iter([
                            Dependency::from(1),
                            Dependency::from(2)
                        ])])
                    ),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::from_iter([
                            Dependency::from(1),
                            Dependency::from(2)
                        ]),
                        is_basis: true,
                    },
                    (2, BTreeSet::new()),
                ),
                (
                    DependencyCell {
                        spanning_deps: DependencySet::empty(),
                        is_basis: true,
                    },
                    (2, BTreeSet::new()),
                ),
            ])
        );

        assert_eq!(
            cell_rep.spanning_dep_counts,
            HashMap::from_iter([(Dependency::from(1), 4), (Dependency::from(2), 4)])
        );

        assert_eq!(
            cell_rep.comb_dep_counts,
            HashMap::from_iter([(
                DependencySet::from_iter([Dependency::from(1), Dependency::from(2)]),
                4
            )])
        );
    }

    #[test]
    fn cell_rep_possible_deps() {
        for n in 0..10 {
            for m in 0..10 {
                {
                    let cell_rep = DependencyPartition::from_dim(n);

                    let possible_deps = cell_rep.possible_deps(m).collect_vec();
                    if n + 1 < m || m == 0 {
                        assert_eq!(possible_deps, vec![]);
                    } else {
                        assert_eq!(
                            possible_deps,
                            vec![BTreeSet::from_iter([(&DependencyCell::new(true), m)])]
                        );
                    }
                }
            }
        }

        {
            let mut cell_rep = DependencyPartition::from_dim(5);
            cell_rep.add_dep(BTreeSet::from_iter([(&DependencyCell::new(true), 3)]));

            assert!(!cell_rep.possible_deps(3).any(|dep| {
                BTreeSet::from_iter(dep.into_iter())
                    == BTreeSet::from_iter([(
                        &DependencyCell {
                            spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                            is_basis: true,
                        },
                        3,
                    )])
            }));
        }

        {
            let mut cell_rep = DependencyPartition::from_dim(6);
            cell_rep.add_dep(BTreeSet::from_iter([(&DependencyCell::new(true), 3)]));
            cell_rep.add_dep(BTreeSet::from_iter([
                (
                    &DependencyCell {
                        spanning_deps: DependencySet::from_iter([Dependency::from(1)]),
                        is_basis: true,
                    },
                    2,
                ),
                (
                    &DependencyCell {
                        spanning_deps: DependencySet::empty(),
                        is_basis: true,
                    },
                    1,
                ),
            ]));

            assert!(
                !cell_rep
                    .possible_deps(5)
                    .any(|dep: BTreeSet<(&DependencyCell, usize)>| {
                        dep.iter().any(|(cell, _)| !cell.is_basis)
                    })
            );
        }
    }

    #[test]
    fn dense_graph_from_cell_rep() {
        for n in 0..10 {
            let dense_graph = nauty::DenseGraph::from(&DependencyPartition::from_dim(n));

            let vertex_count = n + 1;
            let set_word_count = SETWORDSNEEDED(vertex_count);

            assert_eq!(
                dense_graph,
                nauty::DenseGraph {
                    graph: empty_graph(set_word_count, vertex_count),
                    partition: Partition::from_indices(&[(0..vertex_count).collect()]),
                    set_word_count,
                    vertex_count,
                }
            );
        }

        let mut cell_rep = DependencyPartition::from_dim(6);
        cell_rep.add_dep(BTreeSet::from_iter([(&DependencyCell::new(true), 3)]));
        let dense_graph = nauty::DenseGraph::from(&cell_rep);

        // Dimension + 1 and the one dependency
        let vertex_count = (6 + 1) + 1 + 1;
        let set_word_count = SETWORDSNEEDED(vertex_count);
        let mut graph = empty_graph(set_word_count, vertex_count);

        // The first 3 vertices correspond to the empty cell
        for i in 5..vertex_count {
            ADDONEEDGE(&mut graph, 0, i, set_word_count);
        }

        assert_eq!(
            dense_graph,
            nauty::DenseGraph {
                graph,
                partition: Partition::from_indices(&[vec![0], (1..vertex_count).collect()]),
                set_word_count,
                vertex_count,
            }
        );
    }
}
