use arbitrary::Arbitrary;
use compact_bytes::CompactBytes;

#[derive(Debug, Arbitrary)]
pub struct Scenario<'a> {
    creation: Creation<'a>,
    actions: Vec<Action<'a>>,
}

impl Scenario<'_> {
    pub fn run(self) {
        let (mut compact, mut control) = self.creation.create();

        for action in self.actions {
            action.run(&mut compact, &mut control);

            assert_eq!(compact, control);
            assert_eq!(compact.len(), control.len());
            assert_eq!(format!("{compact:?}"), format!("{control:?}"));
        }

        let compact_vec = compact.into_vec();
        assert_eq!(compact_vec, control);
    }
}

#[derive(Debug, Arbitrary)]
pub enum Creation<'a> {
    Bytes(&'a [u8]),
    WithCapacity(u16),
    Vec(Vec<u8>),
}

impl Creation<'_> {
    pub fn create(self) -> (CompactBytes, Vec<u8>) {
        match self {
            Creation::Bytes(slice) => {
                let compact = CompactBytes::new(slice);
                let control = slice.to_vec();

                (compact, control)
            }
            Creation::WithCapacity(capacity) => {
                let compact = CompactBytes::with_capacity(capacity as usize);
                let control = Vec::with_capacity(capacity as usize);

                (compact, control)
            }
            Creation::Vec(v) => {
                let compact = CompactBytes::from(v.clone());
                (compact, v)
            }
        }
    }
}

#[derive(Debug, Arbitrary)]
pub enum Action<'a> {
    Push(u8),
    Extend(&'a [u8]),
    Truncate(usize),
    Clear,
    Reserve(u16),
    Clone,
}

impl Action<'_> {
    pub fn run(self, compact: &mut CompactBytes, control: &mut Vec<u8>) {
        match self {
            Action::Push(b) => {
                compact.push(b);
                control.push(b);
            }
            Action::Extend(slice) => {
                compact.extend_from_slice(slice);
                control.extend_from_slice(slice);
            }
            Action::Truncate(amt) => {
                let amt = if compact.is_empty() {
                    0
                } else {
                    amt % compact.len()
                };

                compact.truncate(amt);
                control.truncate(amt);
            }
            Action::Clear => {
                compact.clear();
                control.clear();
            }
            Action::Reserve(amt) => {
                compact.reserve(amt as usize);
                control.reserve(amt as usize);
            }
            Action::Clone => {
                let compact_ = compact.clone();
                *compact = compact_;

                let control_ = control.clone();
                *control = control_;
            }
        }
    }
}
