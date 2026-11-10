//! Inductive blocks. TEMPORARY STUB: nothing is checked yet. The real checker (docs/CHECKER.md
//! section 3) replaces this function; the signature is the contract.

use crate::env::NameId;
use crate::tc::{Checker, R};

// TODO(real implementation follows in a later change)
pub fn check_inductive(tc: &mut Checker, pos: u32, types: &[NameId], ctors: &[NameId], recs: &[NameId]) -> R<()> {
    let _ = (tc, pos, types, ctors, recs);
    Ok(())
}
