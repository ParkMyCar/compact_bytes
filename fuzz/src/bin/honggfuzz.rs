use compact_bytes_fuzz::Scenario;
use honggfuzz::fuzz;

pub fn main() {
    loop {
        fuzz!(|scenario: Scenario<'_>| { scenario.run() });
    }
}
