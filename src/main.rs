use std::time::Instant;

fn main() {
    let start = Instant::now();
    ag2n_iso::complete_graph_gen(8);
    println!("{:#?}", start.elapsed());
}
