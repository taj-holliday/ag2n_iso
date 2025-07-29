use itertools::Itertools;
use std::fmt;

/// Dependencies are represented by integers which uniquely identify them.
///
/// This is a result of how `DependencyPartition` works.
pub type Dependency = usize;

/// A set of dependencies.
///
/// For performance, the set is stored in a single `u64`. This allows storage of
/// any combination of dependencies between 0 and 63.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DependencySet {
    deps: u64,
}

impl DependencySet {
    pub const EMPTY: Self = Self { deps: 0 };

    pub fn insert(&mut self, dep: Dependency) {
        assert!((self.deps >> dep) % 2 == 0);

        self.deps |= 1 << dep
    }

    pub fn contains(&self, dep: &Dependency) -> bool {
        (self.deps >> dep) % 2 == 1
    }

    pub fn copy_with(&self, addend: Dependency) -> Self {
        let mut copy = *self;
        copy.insert(addend);
        copy
    }
}

impl FromIterator<Dependency> for DependencySet {
    fn from_iter<T: IntoIterator<Item = Dependency>>(iter: T) -> Self {
        let mut new = Self::EMPTY;
        iter.into_iter().for_each(|dep| new.insert(dep));
        new
    }
}

impl fmt::Debug for DependencySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", (*self).into_iter().collect_vec())
    }
}

impl IntoIterator for DependencySet {
    type Item = Dependency;
    type IntoIter = DependencySetIter;

    fn into_iter(self) -> Self::IntoIter {
        DependencySetIter {
            set: self,
            index: 0,
        }
    }
}

/// An iterator over a `DependencySet`.
pub struct DependencySetIter {
    set: DependencySet,
    index: u8,
}

impl Iterator for DependencySetIter {
    type Item = Dependency;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.index >= 64 {
                return None;
            }

            if self.set.contains(&(self.index as usize)) {
                let index = self.index as usize;
                self.index += 1;
                return Some(index);
            }

            self.index += 1;
        }
    }
}
