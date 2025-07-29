use ag2n_iso::dependency_partition::DependencyPartition;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use hashbrown::HashSet;

pub fn criterion_benchmark(c: &mut Criterion) {
    for dim in 0..=8 {
        c.bench_with_input(BenchmarkId::new("cap_finder", dim), &dim, |b, dim| {
            b.iter(|| {
                let mut caps =
                    HashSet::<DependencyPartition>::from_iter([DependencyPartition::basis(*dim)]);

                while !caps.is_empty() {
                    caps = caps
                        .iter()
                        .flat_map(|cap| {
                            (5..=*dim + 1)
                                .step_by(2)
                                .flat_map(|odd| cap.add_possible_deps(odd))
                        })
                        .filter(|rep| *rep.dep_size_map().get(&4).unwrap_or(&0) == 0)
                        .collect();
                }
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
