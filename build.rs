#[cfg(feature = "little-skeptic")]
extern crate little_skeptic;

fn main() {
    #[cfg(feature = "little-skeptic")]
    little_skeptic::generate_doc_tests(&["README.md"]);
}
