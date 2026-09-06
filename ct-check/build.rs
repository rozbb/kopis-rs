//! Compiles `shim.c`, which needs Valgrind's client-request headers.

use std::{env, path::PathBuf};

/// Directories that hold `valgrind/memcheck.h` on the platforms we care about.
const HEADER_SEARCH_DIRS: &[&str] = &[
    "/usr/include",
    "/usr/local/include",
    "/opt/homebrew/include",
    "/usr/local/opt/valgrind/include",
];

fn main() {
    println!("cargo::rerun-if-changed=shim.c");
    println!("cargo::rerun-if-env-changed=VALGRIND_INCLUDE_DIR");

    let mut build = cc::Build::new();
    build.file("shim.c").warnings(true);

    // An explicit override wins; otherwise probe the usual locations so that a missing Valgrind
    // install produces an actionable message instead of a bare "file not found" from the C
    // compiler.
    match env::var_os("VALGRIND_INCLUDE_DIR") {
        Some(dir) => {
            build.include(PathBuf::from(dir));
        }
        None => {
            let found = HEADER_SEARCH_DIRS
                .iter()
                .find(|d| PathBuf::from(d).join("valgrind/memcheck.h").is_file());
            match found {
                Some(dir) => {
                    build.include(dir);
                }
                None => panic!(
                    "ct-check: could not find `valgrind/memcheck.h`.\n\
                     Install the Valgrind headers (Debian/Ubuntu: `sudo apt install valgrind`, \
                     Fedora: `sudo dnf install valgrind-devel`, macOS: `brew install valgrind`), \
                     or point VALGRIND_INCLUDE_DIR at the directory containing `valgrind/`.\n\
                     Searched: {}",
                    HEADER_SEARCH_DIRS.join(", ")
                ),
            }
        }
    }

    build.compile("kopis_ct_shim");
}
