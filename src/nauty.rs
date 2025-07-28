//! This module provides the bare minimum to get the canonical form of a colored
//! graph using Nauty, which can be found here: <https://pallini.di.uniroma1.it/>.

use nauty_Traces_sys::*;
use std::{ffi::c_int, ptr};

// Inspired by graph-canon (https://crates.io/crates/graph-canon), I just needed coloring which it didn't provide...
pub const OPTIONS: optionblk = optionblk {
    getcanon: 1,
    digraph: FALSE,
    writeautoms: FALSE,
    writemarkers: FALSE,
    // false because we care about coloring
    defaultptn: FALSE,
    cartesian: FALSE,
    linelength: 0,
    outfile: ptr::null_mut(),
    userrefproc: None,
    userautomproc: None,
    userlevelproc: None,
    usernodeproc: None,
    usercanonproc: None,
    invarproc: None,
    // TODO: profile changes to tc_level, invarlevel settings
    tc_level: 0,
    mininvarlevel: 0,
    maxinvarlevel: 1,
    invararg: 0,
    dispatch: &raw mut dispatch_graph,
    // also profile schreier
    schreier: FALSE,
    extra_options: ptr::null_mut(),
};

// TODO: profile sparse graph
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DenseGraph {
    pub graph: Vec<setword>,
    pub partition: Partition,
    pub set_word_count: usize,
    pub vertex_count: usize,
}

impl DenseGraph {
    pub fn into_canon_labeling(&mut self, options: &mut optionblk) -> CanonLabeling {
        let mut canon_labeling = empty_graph(self.set_word_count, self.vertex_count);
        let mut orbits = vec![0; self.vertex_count];

        unsafe {
            densenauty(
                self.graph.as_mut_ptr(),
                self.partition.labels.as_mut_ptr(),
                self.partition.partition.as_mut_ptr(),
                orbits.as_mut_ptr(),
                &mut *options,
                &mut statsblk::default(),
                self.set_word_count as c_int,
                self.vertex_count as c_int,
                canon_labeling.as_mut_ptr(),
            )
        }

        CanonLabeling {
            graph: canon_labeling,
            set_word_count: self.set_word_count,
            vertex_count: self.vertex_count,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Partition {
    labels: Vec<c_int>,
    partition: Vec<c_int>,
}

impl Partition {
    pub fn from_indices(indices: &[Vec<usize>]) -> Self {
        let count = indices.iter().map(|slice| slice.len()).sum();
        let (mut labels, mut partition) = (Vec::with_capacity(count), Vec::with_capacity(count));

        for part in indices {
            for index in part {
                labels.push(*index as c_int);
                partition.push(1);
            }

            if let Some(last) = partition.last_mut() {
                *last = 0;
            }
        }

        Self { labels, partition }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct CanonLabeling {
    pub graph: Vec<setword>,
    pub set_word_count: usize,
    pub vertex_count: usize,
}

// TODO: more comprehensive tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partition_from_indices() {
        let (v1, v2) = (vec![3, 2, 5, 1, 0], vec![4, 6, 9]);
        let indices = vec![v1, v2];
        let partition = Partition::from_indices(&indices);

        assert_eq!(vec![3, 2, 5, 1, 0, 4, 6, 9], partition.labels);
        assert_eq!(vec![1, 1, 1, 1, 0, 1, 1, 0], partition.partition);
    }
}
