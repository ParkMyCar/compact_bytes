#![no_main]

use compact_bytes_fuzz::Scenario;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|scenario: Scenario<'_>| scenario.run());
