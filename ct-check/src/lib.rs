//! Secret-tagging primitives for the constant-time harness.
//!
//! The technique is the one BoringSSL and the reference PQC implementations use, sometimes
//! called *ctgrind*: tag every secret byte as **undefined** memory, then run the code under
//! Valgrind's Memcheck. Memcheck already reports "conditional jump depends on uninitialised
//! value" and "address depends on uninitialised value", and those two diagnostics are exactly
//! the definition of a timing side channel — a branch or a memory access whose behaviour is a
//! function of a secret. Definedness propagates bit-precisely through arithmetic, so purely
//! arithmetic code (rotations, masks, `subtle`'s selects) stays silent no matter how much
//! secret data flows through it.
//!
//! Two properties are worth keeping in mind when reading a report:
//!
//! * It only ever sees the path that actually executed. A leak in a branch this run never took
//!   goes unreported, so the harness drives several distinct inputs per operation.
//! * It has no false negatives on the code it *did* run, including hand-written SIMD, because
//!   it works on the executed instruction stream rather than on source.
//!
//! Outside Valgrind every function here is a few no-op instructions, so a plain `cargo run`
//! still exercises the harness (just without any checking).

use core::ffi::c_void;

unsafe extern "C" {
    fn kopis_ct_make_undefined(p: *mut c_void, n: usize);
    fn kopis_ct_make_defined(p: *mut c_void, n: usize);
    fn kopis_ct_running_on_valgrind() -> i32;
}

/// Whether this process is running under Valgrind. When false, [`classify`] and [`declassify`]
/// do nothing and no checking happens.
pub fn under_valgrind() -> bool {
    unsafe { kopis_ct_running_on_valgrind() != 0 }
}

/// Marks `v`'s bytes secret. From here on, any branch taken on them or any address computed
/// from them is reported as an error.
///
/// This covers the whole in-memory footprint of `v`, padding included, which is what we want:
/// over-tagging can only cause a report, never suppress one.
///
/// The `&mut` is load-bearing and not just good manners. Tagging is invisible to the optimiser —
/// it is a no-op instruction sequence — so if this took `&T`, LLVM would treat the pointer as
/// read-only, keep believing it knows what the buffer holds, and constant-fold the very loads
/// and branches we are trying to observe. The checks then pass because the code under test was
/// deleted. Taking `&mut` forces LLVM to assume the callee overwrote the buffer with something
/// unknowable, which is exactly the view Memcheck has of it. `ct-check.sh --selftest` exists to
/// catch a regression here.
pub fn classify<T: ?Sized>(v: &mut T) {
    let len = core::mem::size_of_val(v);
    unsafe { kopis_ct_make_undefined(v as *mut T as *mut c_void, len) }
}

/// Marks `v`'s bytes public again.
///
/// A shared reference is fine here: this direction only ever removes tags, so the optimiser
/// keeping a stale idea of the contents cannot hide a leak.
///
/// Used for two things: releasing an operation's outputs so the harness can checksum them
/// without tripping over its own tags, and whitelisting a value the design deliberately leaks.
pub fn declassify<T: ?Sized>(v: &T) {
    let len = core::mem::size_of_val(v);
    unsafe { kopis_ct_make_defined(v as *const T as *mut c_void, len) }
}

/// Folds bytes into a single value, so the harness can consume a result without the optimiser
/// deleting the work that produced it.
pub fn checksum(bytes: &[u8]) -> u8 {
    bytes.iter().fold(0u8, |acc, b| acc ^ b)
}
