use std::cmp;

pub struct RestrictedPartitionIterator {
    part_sizes: Vec<usize>,
    stack: Vec<(Vec<usize>, usize)>,
    empty: bool,
}

impl RestrictedPartitionIterator {
    pub fn new(part_sizes: Vec<usize>, n: usize) -> Self {
        let mut empty = false;
        if n > part_sizes.iter().sum() || n == 0 {
            empty = true;
        }

        Self {
            part_sizes,
            stack: vec![(vec![], n)],
            empty,
        }
    }
}

impl Iterator for RestrictedPartitionIterator {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.empty {
            return None;
        }

        while let Some((state, remaining)) = self.stack.pop() {
            if remaining == 0 {
                return Some(state);
            }

            if state.len() == self.part_sizes.len() {
                continue;
            }

            for count in 0..=cmp::min(self.part_sizes[state.len()], remaining) {
                let mut next_state = Vec::with_capacity(state.len() + 1);
                next_state.extend_from_slice(&state);
                next_state.push(count);
                self.stack.push((next_state, remaining - count));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn restricted_partition_iterator_test() {
        for n in 0..10 {
            assert_eq!(
                Vec::<Vec<usize>>::new(),
                RestrictedPartitionIterator::new(vec![0; n], 1).collect::<Vec<_>>()
            );

            assert_eq!(
                Vec::<Vec<usize>>::new(),
                RestrictedPartitionIterator::new(vec![0; 1], n).collect::<Vec<_>>()
            );

            assert_eq!(
                Vec::<Vec<usize>>::new(),
                RestrictedPartitionIterator::new(vec![1; n], n + 1).collect::<Vec<_>>()
            );

            assert_eq!(
                Vec::<Vec<usize>>::new(),
                RestrictedPartitionIterator::new(vec![2; n], 2 * n + 1).collect::<Vec<_>>()
            );
        }

        for n in 1..10 {
            assert_eq!(
                vec![vec![1; n]],
                RestrictedPartitionIterator::new(vec![1; n], n).collect::<Vec<_>>()
            );
        }

        for n in 2..10 {
            assert_eq!(
                HashSet::from_iter((0..n).map(|i| {
                    let mut partition = vec![1; n];
                    partition[i] = 0;
                    if let Some(0) = partition.last() {
                        partition.pop();
                    }
                    partition
                })),
                RestrictedPartitionIterator::new(vec![1; n], n - 1).collect::<HashSet<_>>()
            );
        }

        assert_eq!(
            HashSet::from_iter([
                vec![1, 2, 1],
                vec![1, 1, 2],
                vec![1, 0, 3],
                vec![0, 2, 2],
                vec![0, 1, 3],
            ]),
            RestrictedPartitionIterator::new(vec![1, 2, 3], 4).collect::<HashSet<_>>()
        );
    }
}
