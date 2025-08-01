//! This module provides a representation of a dependency partition with methods
//! to incrementally generate partitions and determine affine equivalence.

use crate::{
    dependency::{Dependency, DependencySet},
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

/// A dependency specification.
///
/// Because partitions generated with a spanning set of dependencies are the
/// same as partitions generated with the full linear subspace of dependencies,
/// this program only fills dependency specifications with dependencies from a
/// spanning set. To learn more, look at the docs for `DependencyPartition`.
pub type DependencySpec = DependencySet;

/// A linear combination of dependencies.
///
/// Instead of storing the dependency itself, we store the set of dependencies
/// which sum to this one.
pub type CombDependency = DependencySet;

/// Describes the vectors of a dependency cell.
///
/// This is done in terms of the number of basis vectors and the number of
/// 'comb' vectors contained within it. 'comb' is short for combination, so
/// `comb_count` gives the number of vectors which are affine combinations of
/// the basis vectors.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CellData {
    pub comb_count: usize,
    pub basis_count: usize,
}

impl CellData {
    pub fn new(comb_count: usize, basis_count: usize) -> Self {
        Self {
            comb_count,
            basis_count,
        }
    }

    /// Generates a new `CellData` instance with `basis_count` basis vectors and
    /// no comb vectors.
    pub fn basis(basis_count: usize) -> Self {
        Self {
            comb_count: 0,
            basis_count,
        }
    }

    /// Generates a new `CellData` instance with `comb_count` comb vectors and
    /// no basis vectors.
    pub fn comb(comb_count: usize) -> Self {
        Self {
            comb_count,
            basis_count: 0,
        }
    }

    /// Gives the total number of vectors of the cell.
    pub fn vec_count(&self) -> usize {
        self.basis_count + self.comb_count
    }
}

/// Type representing a dependency partition.
///
/// # Description
///
/// `spanning_dep_counts` and `comb_dep_counts` are just memoized maps giving
/// the number of vectors in each dependency.
///
/// `cells` is a map which is analogous to the dependency partition function. It
/// takes in a dependency specification, and returns some useful information
/// about the corresponding cell. Namely, contained in the `CellData` component
/// we are given the number of vectors and basis vectors in each cell.
///
/// It isn't quite that simple, though, as we also have a
/// `BTreeSet<CombDependency>` component. Why?
///
/// A dependency partition is fully described by a spanning set of dependencies.
/// Thus each dependency specification need only holds a subset of a spanning
/// set of dependencies as opposed to a subset of all dependencies.
///
/// However, it's still useful to have the complete set of dependencies around.
/// For example, finding the graph representation of a dependency partition
/// requires the set all dependencies. We could just generate the set from our
/// spanning set, but I ended up just caching it in our
/// `BTreeSet<CombDependency>`.
///
/// Hence the `BTreeSet<CombDependency>` is a set of all dependencies
/// corresponding to the cell which are a linear combination of our spanning set
/// of dependencies.
///
/// Note that this means that our dependency specifications are all created from
/// a set of spanning dependencies.
///
/// To explain which set of spanning dependencies, note that `CellData` has a
/// field giving the number of basis elements of a cell. This implies that each
/// `DependencyPartition` has a basis, which is correct. Then given a basis `B =
/// { b_1, ..., b_n }` of `V` with `D = V \ B`, it's true that the set `S` of
/// dependencies with exactly one element of `D` in them spans all dependencies
/// of `V`. For this program we have chosen the set `S`.
///
/// Finally, note that `CombDependency` is a type alias for `DependencySet`.
/// This is because each `CombDependency` stores the subset of our spanning
/// dependencies which sum to it.
///
/// # Use
/// This struct provides methods which allow you to incrementally generate at
/// least one representative of each affine equivalence class of dimension `n`.
/// Namely, if our partition has `k` vecs in `n` dimensions, then
/// `add_possible_deps` will generate all partitions corresponding to
/// `n`-dimensional sets with `k + 1` vecs with the current partition as a
/// subset. We know one partition cannot correspond to two affine equivalence
/// classes, so repeating this process yields at least one representative for
/// each affine equivalence classes in dimension `n`.
///
/// This struct also can be converted into a canonical form for its affine
/// equivalence class. This was done when implementing `PartialEq` and `Hash`,
/// so it's easy to cull a set of `DependencyPartition`s until there is exactly
/// one representative for each affine equivalence class.
///
/// # Example
///
/// Here we generate all affine equivalence classes of dimension `4`.
///
/// ```
/// use ag2n_iso::dependency_partition::DependencyPartition;
/// use std::collections::HashSet;
///
/// let dim = 4;
///
/// let mut acc = HashSet::new();
/// let mut sets = HashSet::<DependencyPartition>::from_iter([DependencyPartition::basis(dim)]);
///
/// while !sets.is_empty() {
///     acc.extend(sets.clone());
///
///     sets = sets
///         .iter()
///         .flat_map(|set| {
///             (3..=dim + 1)
///                 .step_by(2)
///                 .flat_map(|odd| set.add_possible_deps(odd))
///         })
///         .collect();
/// }
///
/// println!("{} affine equivalence classes", acc.len());
/// ```
#[derive(Clone)]
pub struct DependencyPartition {
    cells: BTreeMap<DependencySpec, (CellData, BTreeSet<CombDependency>)>,
    spanning_dep_counts: HashMap<Dependency, usize>,
    comb_dep_counts: HashMap<DependencySet, usize>,
}

impl DependencyPartition {
    /// Generates a `DependencyPartition` representing an affinely independent
    /// set of dimension `dim`.
    pub fn basis(dim: usize) -> Self {
        Self {
            cells: BTreeMap::from_iter([(
                DependencySpec::EMPTY,
                (CellData::basis(dim + 1), BTreeSet::new()),
            )]),
            spanning_dep_counts: HashMap::new(),
            comb_dep_counts: HashMap::new(),
        }
    }

    /// WIP. See the Quad128 paper.
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

                for (spec, (cell_data, _)) in &self.cells {
                    let mut pass = true;
                    for (_, dep) in &comb {
                        if !spec.contains(dep) {
                            pass = false;
                            break;
                        }
                    }

                    if pass {
                        count += cell_data.vec_count();
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

    /// Generates a map which takes some integer `n` and returns the number of
    /// dependencies of the `DependencyPartition` which contain `n` vectors.
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

    /// Number of vectors.
    pub fn vec_count(&self) -> usize {
        self.basis_len() + self.spanning_dep_counts.iter().count()
    }

    /// Number of basis vectors.
    pub fn basis_len(&self) -> usize {
        self.cells
            .iter()
            .map(|(_, (cell_data, _))| cell_data.basis_count)
            .sum()
    }

    /// Dimension of the set.
    pub fn dim(&self) -> usize {
        self.basis_len() - 1
    }

    /// Map which takes a spanning dependency and returns the number of
    /// vectors it contains.
    pub fn spanning_dep_counts(&self) -> &HashMap<Dependency, usize> {
        &self.spanning_dep_counts
    }

    /// Map which takes a combination dependency and returns the number of
    /// vectors it contains.
    pub fn comb_dep_counts(&self) -> &HashMap<CombDependency, usize> {
        &self.comb_dep_counts
    }

    /// Extend the basis by 1 element.
    pub fn add_indep_vec(&mut self) {
        let spec = DependencySpec::EMPTY;
        self.cells
            .entry(spec)
            .and_modify(|(cell_data, _)| cell_data.basis_count += 1)
            .or_insert((CellData::basis(1), BTreeSet::new()));
    }

    /// If the current `DependencyPartition` represents set `V`, then this
    /// function returns an iterator over the set of all dependency partitions
    /// `{ V U {v_1}, ..., V U {v_n} }` such that `v_i` is the sum of `size`
    /// basis elements.
    pub fn add_possible_deps(&self, size: usize) -> impl Iterator<Item = Self> {
        self.possible_deps(size).map(move |dep| {
            let mut clone = self.clone();
            clone.add_dep(dep);
            clone
        })
    }

    /// If `self` represents the set `V`, this function returns an iterator over
    /// affine combinations `{ v_1, ..., v_n }` of the basis with `size`
    /// vectors such that the set `{ V U {v_1}, ..., V U {v_n} }` gives all
    /// possible partition equivalence classes of the form `V U v`, where `v` is
    /// an affine combination of `size` elements of the basis.
    pub fn possible_deps(
        &self,
        size: usize,
    ) -> impl Iterator<Item = BTreeSet<(&DependencySpec, usize)>> {
        // All possible dependencies can be expressed as a sum of basis elements
        let basis = self
            .cells
            .iter()
            .filter(|(_, (cell_data, _))| cell_data.basis_count > 0)
            .collect_vec();

        // Take all partitions of elements among the dependency cells of the basis
        RestrictedPartitionIterator::new(
            basis
                .iter()
                .map(|(_, (cell_data, _))| cell_data.basis_count)
                .collect_vec(),
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
                    .filter_map(|(spec, (cell_data, _))| {
                        if let Some((_, dep_count)) =
                            dep.iter().find(|(dep_spec, _)| *dep_spec == spec)
                        {
                            Some(if spec.contains(other_dep) {
                                cell_data.vec_count() - dep_count
                            } else {
                                cell_data.vec_count()
                            })
                        } else {
                            spec.contains(other_dep).then_some(cell_data.vec_count())
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
                    .filter_map(|(spec, (cell_data, comb_deps))| {
                        if let Some((_, dep_count)) =
                            dep.iter().find(|(dep_spec, _)| *dep_spec == spec)
                        {
                            Some(if comb_deps.contains(other_dep) {
                                cell_data.vec_count() - dep_count
                            } else {
                                cell_data.vec_count()
                            })
                        } else {
                            comb_deps
                                .contains(other_dep)
                                .then_some(cell_data.vec_count())
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

    /// Adds a dependency to the partition.
    pub fn add_dep(&mut self, dep: BTreeSet<(&DependencySpec, usize)>) {
        // The dependency cannot have any redundant cells
        assert!(!dep.iter().any(|(_, count)| *count == 0));

        // Add dependency

        let dep_marker = Dependency::from(
            self.spanning_dep_counts
                .keys()
                .map(|dep| dep + 1)
                .max()
                .unwrap_or(0),
        );

        // Split cells
        for (spec, dep_count) in &dep {
            let (cell_data, comb_deps) = self.cells.get_mut(spec).unwrap();
            let comb_deps = comb_deps.clone();
            cell_data.basis_count -= *dep_count;

            if cell_data.vec_count() == 0 {
                self.cells.remove(spec);
            }

            let mut new_spec = **spec;
            new_spec.insert(dep_marker);
            self.cells
                .insert(new_spec, (CellData::basis(*dep_count), comb_deps));
        }

        // Add final cell
        let spec = DependencySpec::from_iter([dep_marker]);
        self.cells
            .entry(spec)
            .and_modify(|(cell_data, _)| cell_data.comb_count += 1)
            .or_insert((CellData::comb(1), BTreeSet::new()));

        // Update spanning dependency counts
        self.spanning_dep_counts.insert(
            dep_marker,
            dep.iter().map(|(_, count)| count).sum::<usize>() + 1,
        );

        // Add implied dependencies

        let mut delta = HashMap::<DependencySpec, BTreeSet<DependencySet>>::new();
        let mut dep_count_delta = HashMap::new();

        // Sum of this dep + spanning deps
        for spanning_dep in self
            .spanning_dep_counts
            .keys()
            .filter(|spanning_dep| **spanning_dep != dep_marker)
        {
            let new_comb_dep = DependencySet::from_iter([dep_marker, *spanning_dep]);

            let mut dep_count = 0;
            for (spec, (cell_data, _)) in self
                .cells
                .iter()
                .filter(|(spec, _)| spec.contains(spanning_dep) ^ spec.contains(&dep_marker))
            {
                if let Some(deps) = delta.get_mut(spec) {
                    deps.insert(new_comb_dep);
                } else {
                    delta.insert(*spec, BTreeSet::from_iter([new_comb_dep]));
                }
                dep_count += cell_data.vec_count();
            }

            dep_count_delta.insert(new_comb_dep, dep_count);
        }

        // Sum of this dep + other comb deps
        for comb_dep in self.comb_dep_counts.keys() {
            let new_comb_dep = comb_dep.copy_with(dep_marker);

            let mut dep_count = 0;
            for (spec, (cell_data, _)) in self.cells.iter().filter(|(spec, (_, comb_deps))| {
                comb_deps.contains(comb_dep) ^ spec.contains(&dep_marker)
            }) {
                if let Some(deps) = delta.get_mut(spec) {
                    deps.insert(new_comb_dep);
                } else {
                    delta.insert(*spec, BTreeSet::from_iter([new_comb_dep]));
                }
                dep_count += cell_data.vec_count();
            }

            dep_count_delta.insert(new_comb_dep, dep_count);
        }

        // Insert comb deps
        for (spec, mut new_comb_deps) in delta {
            let (_, comb_deps) = self.cells.get_mut(&spec).unwrap();
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

        let vertex_count = value
            .cells
            .values()
            .map(|(cell_data, _)| cell_data.vec_count())
            .sum::<usize>()
            + spanning_dep_count
            + comb_dep_count;
        let set_word_count = SETWORDSNEEDED(vertex_count);
        let mut graph = empty_graph(set_word_count, vertex_count);

        let spanning_dep_indices = HashMap::<Dependency, usize>::from_iter(
            value
                .spanning_dep_counts
                .keys()
                .enumerate()
                .map(|(i, spanning_dep)| (*spanning_dep, i)),
        );

        let comb_dep_indices = HashMap::<DependencySet, usize>::from_iter(
            value
                .comb_dep_counts
                .keys()
                .enumerate()
                .map(|(i, comb_dep)| (*comb_dep, i + spanning_dep_count)),
        );

        let mut cell_i = spanning_dep_count + comb_dep_count;
        for (spec, (cell_data, comb_deps)) in &value.cells {
            for vec_i in 0..cell_data.vec_count() {
                for spanning_dep in spec.into_iter() {
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

            cell_i += cell_data.vec_count();
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
        // Sort the cells nicely
        let mut cells = self.cells.iter().collect_vec();
        cells.sort_by(|(spec1, (cell_data1, _)), (spec2, (cell_data2, _))| {
            let ord = cell_data2.basis_count.cmp(&cell_data1.basis_count);
            if ord == Ordering::Equal {
                let mut deps = spec1.into_iter().chain(**spec2).unique().collect_vec();
                deps.sort();

                for dep in deps {
                    let ord = spec2.contains(&dep).cmp(&spec1.contains(&dep));

                    if ord != Ordering::Equal {
                        return ord;
                    }
                }

                Ordering::Equal
            } else {
                ord
            }
        });

        // Sort the spanning deps
        let mut spanning_dep_counts = self.spanning_dep_counts.iter().collect_vec();
        spanning_dep_counts.sort();

        // Print spanning deps
        for (dep, _) in &spanning_dep_counts {
            for (cell, (cell_data, _)) in &cells {
                if cell.contains(dep) {
                    for _ in 0..cell_data.vec_count() {
                        write!(f, "▏▂▂ ")?;
                    }
                } else {
                    for _ in 0..cell_data.vec_count() {
                        write!(f, "▏   ")?;
                    }
                }
            }
            writeln!(f, "▏{dep}")?;
        }

        // (optional) Print the comb deps
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

        // Print markers for basis elements
        for (_, (cell_data, _)) in &cells {
            for i in 0..cell_data.vec_count() {
                if i < cell_data.basis_count {
                    write!(f, "▏BA ")?;
                } else {
                    write!(f, "▏   ")?;
                }
            }
        }
        writeln!(f, "▏")?;

        // Print vector labels
        for i in 0..cells
            .iter()
            .map(|(_, (cell_data, _))| cell_data.vec_count())
            .sum()
        {
            write!(f, "▏")?;
            if i < 10 {
                write!(f, "0")?;
            }
            write!(f, "{i} ")?;
        }
        write!(f, "▏")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nauty::Partition;
    use core::iter::Iterator;

    #[test]
    fn spanning_dependency_set() {
        let set = DependencySet::from_iter([1, 5, 7, 25]);

        for i in 0..64 {
            if i == 1 || i == 5 || i == 7 || i == 25 {
                assert!(set.contains(&i));
            } else {
                assert!(!set.contains(&i));
            }
        }

        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(5));
        assert_eq!(iter.next(), Some(7));
        assert_eq!(iter.next(), Some(25));
    }

    #[test]
    fn cell_rep_new() {
        for n in 0..10 {
            let cell_rep = DependencyPartition::basis(n);
            assert_eq!(
                cell_rep,
                DependencyPartition {
                    cells: BTreeMap::from_iter([(
                        DependencySpec::EMPTY,
                        (CellData::basis(n + 1), BTreeSet::new())
                    )]),
                    spanning_dep_counts: HashMap::new(),
                    comb_dep_counts: HashMap::new(),
                }
            );
        }
    }

    #[test]
    fn cell_rep_add_dependency() {
        let mut cell_rep = DependencyPartition::basis(5);
        cell_rep.add_dep(BTreeSet::from_iter([(&DependencySpec::EMPTY, 3)]));

        // |__|__|__|  |  |  |__|
        // |1 |2 |3 |4 |5 |6 |7 |
        // | basis           | not basis

        assert_eq!(
            cell_rep.cells,
            BTreeMap::from_iter([
                (
                    DependencySpec::from_iter([0]),
                    (CellData::new(1, 3), BTreeSet::new())
                ),
                (DependencySpec::EMPTY, (CellData::basis(3), BTreeSet::new())),
            ])
        );

        assert_eq!(cell_rep.spanning_dep_counts, HashMap::from_iter([(0, 4)]));
        assert_eq!(cell_rep.comb_dep_counts, HashMap::new());

        // spanning:
        // |__|__|__|  |  |  |__|  |: 1
        // |__|__|  |__|  |  |  |__|: 2
        // comb:
        // |  |  |__|__|  |  |__|__|: 1 + 2
        // |1 |2 |3 |4 |5 |6 |7 |8 |
        // | basis           | not basis

        cell_rep.add_dep(BTreeSet::from_iter([
            (&DependencySpec::from_iter([0]), 2),
            (&DependencySpec::EMPTY, 1),
        ]));

        assert_eq!(
            cell_rep.cells,
            BTreeMap::from_iter([
                (
                    DependencySpec::from_iter([0]),
                    (
                        CellData::new(1, 1),
                        BTreeSet::from_iter([CombDependency::from_iter([0, 1])])
                    )
                ),
                (
                    DependencySpec::from_iter([1]),
                    (
                        CellData::new(1, 1),
                        BTreeSet::from_iter([CombDependency::from_iter([0, 1])])
                    )
                ),
                (
                    DependencySpec::from_iter([0, 1]),
                    (CellData::basis(2), BTreeSet::new())
                ),
                (DependencySpec::EMPTY, (CellData::basis(2), BTreeSet::new()))
            ])
        );

        assert_eq!(
            cell_rep.spanning_dep_counts,
            HashMap::from_iter([(0, 4), (1, 4)])
        );

        assert_eq!(
            cell_rep.comb_dep_counts,
            HashMap::from_iter([(DependencySet::from_iter([0, 1]), 4)])
        );
    }

    #[test]
    fn cell_rep_possible_deps() {
        for n in 0..10 {
            for m in 0..10 {
                {
                    let cell_rep = DependencyPartition::basis(n);

                    let possible_deps = cell_rep.possible_deps(m).collect_vec();
                    if n + 1 < m || m == 0 {
                        assert_eq!(possible_deps, vec![]);
                    } else {
                        assert_eq!(
                            possible_deps,
                            vec![BTreeSet::from_iter([(&DependencySpec::EMPTY, m)])]
                        );
                    }
                }
            }
        }

        {
            let mut cell_rep = DependencyPartition::basis(5);
            cell_rep.add_dep(BTreeSet::from_iter([(&DependencySpec::EMPTY, 3)]));

            assert!(!cell_rep.possible_deps(3).any(|dep| {
                BTreeSet::from_iter(dep.into_iter())
                    == BTreeSet::from_iter([(&DependencySpec::from_iter([0]), 3)])
            }));
        }

        {
            let mut cell_rep = DependencyPartition::basis(6);
            cell_rep.add_dep(BTreeSet::from_iter([(&DependencySpec::EMPTY, 3)]));
            cell_rep.add_dep(BTreeSet::from_iter([
                (&DependencySpec::from_iter([0]), 2),
                (&DependencySpec::EMPTY, 1),
            ]));

            assert!(
                !cell_rep
                    .possible_deps(5)
                    .any(|dep: BTreeSet<(&DependencySpec, usize)>| {
                        dep.iter()
                            .any(|(spec, _)| !(cell_rep.cells.get(spec).unwrap().0.basis_count > 0))
                    })
            );
        }
    }

    #[test]
    fn dense_graph_from_cell_rep() {
        for n in 0..10 {
            let dense_graph = nauty::DenseGraph::from(&DependencyPartition::basis(n));

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

        let mut cell_rep = DependencyPartition::basis(6);
        cell_rep.add_dep(BTreeSet::from_iter([(&DependencySpec::EMPTY, 3)]));
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
