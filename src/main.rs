use std::time::Instant;

fn main() {
    let start = Instant::now();
    ag2n_iso::cap_gen_verbose(8);
    println!("{:#?}", start.elapsed());
}
