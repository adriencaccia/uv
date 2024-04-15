#![cfg(all(feature = "python", feature = "pypi"))]

use fs_err as fs;
use std::env::consts::EXE_SUFFIX;
use std::path::Path;
use std::process::Command;

use anyhow::Result;
use assert_cmd::prelude::*;
use assert_fs::fixture::ChildPath;
use assert_fs::prelude::*;
use indoc::indoc;
use predicates::Predicate;
use url::Url;

use common::{create_venv, python_path_with_versions, uv_snapshot, venv_to_interpreter};
use uv_fs::Simplified;

use crate::common::{copy_dir_all, get_bin, TestContext};

mod common;

fn check_command(venv: &Path, command: &str, temp_dir: &Path) {
    Command::new(venv_to_interpreter(venv))
        // Our tests change files in <1s, so we must disable CPython bytecode caching or we'll get stale files
        // https://github.com/python/cpython/issues/75953
        .arg("-B")
        .arg("-c")
        .arg(command)
        .current_dir(temp_dir)
        .assert()
        .success();
}

/// Create a `pip sync` command with options shared across scenarios.
fn command(context: &TestContext) -> Command {
    let mut command = Command::new(get_bin());
    command
        .arg("pip")
        .arg("sync")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", context.venv.as_os_str())
        .env("UV_NO_WRAP", "1")
        .current_dir(&context.temp_dir);

    if cfg!(all(windows, debug_assertions)) {
        // TODO(konstin): Reduce stack usage in debug mode enough that the tests pass with the
        // default windows stack of 1MB
        command.env("UV_STACK_SIZE", (8 * 1024 * 1024).to_string());
    }

    command
}

/// Create a `pip uninstall` command with options shared across scenarios.
fn uninstall_command(context: &TestContext) -> Command {
    let mut command = Command::new(get_bin());
    command
        .arg("pip")
        .arg("uninstall")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", context.venv.as_os_str())
        .env("UV_NO_WRAP", "1")
        .current_dir(&context.temp_dir);

    if cfg!(all(windows, debug_assertions)) {
        // TODO(konstin): Reduce stack usage in debug mode enough that the tests pass with the
        // default windows stack of 1MB
        command.env("UV_STACK_SIZE", (8 * 1024 * 1024).to_string());
    }

    command
}

#[test]
fn missing_pip() {
    uv_snapshot!(Command::new(get_bin()).arg("sync"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: unrecognized subcommand 'sync'

      tip: a similar subcommand exists: 'uv pip sync'

    Usage: uv [OPTIONS] <COMMAND>

    For more information, try '--help'.
    "###);
}

#[test]
fn missing_requirements_txt() {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: failed to read from file `requirements.txt`
      Caused by: No such file or directory (os error 2)
    "###);

    requirements_txt.assert(predicates::path::missing());
}

#[test]
fn missing_venv() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements = context.temp_dir.child("requirements.txt");
    requirements.write_str("anyio")?;
    fs::remove_dir_all(&context.venv)?;

    uv_snapshot!(context.filters(), command(&context).arg("requirements.txt"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: failed to canonicalize path `[VENV]/`
      Caused by: No such file or directory (os error 2)
    "###);

    assert!(predicates::path::missing().eval(&context.venv));

    Ok(())
}

/// Install a package into a virtual environment using the default link semantics. (On macOS,
/// this using `clone` semantics.)
#[test]
fn install() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    // Counterpart for the `compile()` test.
    assert!(!context
        .site_packages()
        .join("markupsafe")
        .join("__pycache__")
        .join("__init__.cpython-312.pyc")
        .exists());

    context.assert_command("import markupsafe").success();

    // Removing the cache shouldn't invalidate the virtual environment.
    fs::remove_dir_all(context.cache_dir.path())?;

    context.assert_command("import markupsafe").success();

    Ok(())
}

/// Install a package into a virtual environment using copy semantics.
#[test]
fn install_copy() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--link-mode")
        .arg("copy")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    context.assert_command("import markupsafe").success();

    // Removing the cache shouldn't invalidate the virtual environment.
    fs::remove_dir_all(context.cache_dir.path())?;

    context.assert_command("import markupsafe").success();

    Ok(())
}

/// Install a package into a virtual environment using hardlink semantics.
#[test]
fn install_hardlink() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--link-mode")
        .arg("hardlink")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    context.assert_command("import markupsafe").success();

    // Removing the cache shouldn't invalidate the virtual environment.
    fs::remove_dir_all(context.cache_dir.path())?;

    context.assert_command("import markupsafe").success();

    Ok(())
}

/// Install multiple packages into a virtual environment.
#[test]
fn install_many() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context
        .assert_command("import markupsafe; import tomli")
        .success();

    Ok(())
}

/// Attempt to install an already-installed package into a virtual environment.
#[test]
fn noop() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 1 package in [TIME]
    "###
    );

    context.assert_command("import markupsafe").success();

    Ok(())
}

/// Install a package into a virtual environment, then install the same package into a different
/// virtual environment.
#[test]
fn link() -> Result<()> {
    let context = TestContext::new("3.12");
    let venv1 = &context.venv;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    Command::new(get_bin())
        .arg("pip")
        .arg("sync")
        .arg("requirements.txt")
        .arg("--strict")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv1.as_os_str())
        .current_dir(&context.temp_dir)
        .assert()
        .success();

    let venv2 = context.temp_dir.child(".venv2");
    let python_path = python_path_with_versions(&context.temp_dir, &["3.12"])
        .expect("Failed to create Python test path");
    Command::new(get_bin())
        .arg("venv")
        .arg(venv2.as_os_str())
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .arg("--python")
        .arg("3.12")
        .env("UV_TEST_PYTHON_PATH", python_path)
        .current_dir(&context.temp_dir)
        .assert()
        .success();
    venv2.assert(predicates::path::is_dir());

    uv_snapshot!(Command::new(get_bin())
        .arg("pip")
        .arg("sync")
        .arg("requirements.txt")
        .arg("--strict")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv2.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    check_command(&venv2, "import markupsafe", &context.temp_dir);

    Ok(())
}

/// Install a package into a virtual environment, then sync the virtual environment with a
/// different requirements file.
#[test]
fn add_remove() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import tomli").success();
    context.assert_command("import markupsafe").failure();

    Ok(())
}

/// Install a package into a virtual environment, then install a second package into the same
/// virtual environment.
#[test]
fn install_sequential() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1
    "###
    );

    context
        .assert_command("import markupsafe; import tomli")
        .success();

    Ok(())
}

/// Install a package into a virtual environment, then install a second package into the same
/// virtual environment.
#[test]
fn upgrade() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tomli==2.0.0")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - tomli==2.0.0
     + tomli==2.0.1
    "###
    );

    context.assert_command("import tomli").success();

    Ok(())
}

/// Install a package into a virtual environment from a URL.
#[test]
fn install_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install a package into a virtual environment from a Git repository.
#[test]
#[cfg(feature = "git")]
fn install_git_commit() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install a package into a virtual environment from a Git repository.
#[test]
#[cfg(feature = "git")]
fn install_git_tag() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ git+https://github.com/pallets/WerkZeug.git@2.0.0")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/WerkZeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install two packages from the same Git repository.
#[test]
#[cfg(feature = "git")]
fn install_git_subdirectories() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("example-pkg-a @ git+https://github.com/pypa/sample-namespace-packages.git@df7530eeb8fa0cb7dbb8ecb28363e8e36bfa2f45#subdirectory=pkg_resources/pkg_a\nexample-pkg-b @ git+https://github.com/pypa/sample-namespace-packages.git@df7530eeb8fa0cb7dbb8ecb28363e8e36bfa2f45#subdirectory=pkg_resources/pkg_b")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + example-pkg-a==1 (from git+https://github.com/pypa/sample-namespace-packages.git@df7530eeb8fa0cb7dbb8ecb28363e8e36bfa2f45#subdirectory=pkg_resources/pkg_a)
     + example-pkg-b==1 (from git+https://github.com/pypa/sample-namespace-packages.git@df7530eeb8fa0cb7dbb8ecb28363e8e36bfa2f45#subdirectory=pkg_resources/pkg_b)
    "###
    );

    context.assert_command("import example_pkg").success();
    context.assert_command("import example_pkg.a").success();
    context.assert_command("import example_pkg.b").success();

    Ok(())
}

/// Install a source distribution into a virtual environment.
#[test]
fn install_sdist() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("Werkzeug==0.9.6")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==0.9.6
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install a source distribution into a virtual environment.
#[test]
fn install_sdist_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("Werkzeug @ https://files.pythonhosted.org/packages/63/69/5702e5eb897d1a144001e21d676676bcb87b88c0862f947509ea95ea54fc/Werkzeug-0.9.6.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==0.9.6 (from https://files.pythonhosted.org/packages/63/69/5702e5eb897d1a144001e21d676676bcb87b88c0862f947509ea95ea54fc/Werkzeug-0.9.6.tar.gz)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Attempt to re-install a package into a virtual environment from a URL. The second install
/// should be a no-op.
#[test]
fn install_url_then_install_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 1 package in [TIME]
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install a package via a URL, then via a registry version. The second install _should_ remove the
/// URL-based version, but doesn't right now.
#[test]
fn install_url_then_install_version() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug==2.0.0")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 1 package in [TIME]
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Install a package via a registry version, then via a direct URL version. The second install
/// should remove the registry-based version.
#[test]
fn install_version_then_install_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug==2.0.0")?;

    command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .assert()
        .success();

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - werkzeug==2.0.0
     + werkzeug==2.0.0 (from https://files.pythonhosted.org/packages/ff/1d/960bb4017c68674a1cb099534840f18d3def3ce44aed12b5ed8b78e0153e/Werkzeug-2.0.0-py3-none-any.whl)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Test that we select the last 3.8 compatible numpy version instead of trying to compile an
/// incompatible sdist <https://github.com/astral-sh/uv/issues/388>
#[test]
fn install_numpy_py38() -> Result<()> {
    let context = TestContext::new("3.8");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("numpy")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + numpy==1.24.4
    "###
    );

    context.assert_command("import numpy").success();

    Ok(())
}

/// Attempt to install a package without using a remote index.
#[test]
fn install_no_index() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--no-index")
        .arg("--strict"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because markupsafe==2.1.3 was not found in the provided package locations and you require markupsafe==2.1.3, we can conclude that the requirements are unsatisfiable.

          hint: Packages were unavailable because index lookups were disabled and no additional package locations were provided (try: `--find-links <uri>`)
    "###
    );

    context.assert_command("import markupsafe").failure();

    Ok(())
}

/// Attempt to install a package without using a remote index
/// after a previous successful installation.
#[test]
fn install_no_index_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    context.assert_command("import markupsafe").success();

    uninstall_command(&context)
        .arg("markupsafe")
        .assert()
        .success();

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--no-index")
        .arg("--strict"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because markupsafe==2.1.3 was not found in the provided package locations and you require markupsafe==2.1.3, we can conclude that the requirements are unsatisfiable.

          hint: Packages were unavailable because index lookups were disabled and no additional package locations were provided (try: `--find-links <uri>`)
    "###
    );

    context.assert_command("import markupsafe").failure();

    Ok(())
}

#[test]
fn warn_on_yanked_version() -> Result<()> {
    let context = TestContext::new("3.12");

    // This version is yanked.
    let requirements_in = context.temp_dir.child("requirements.txt");
    requirements_in.write_str("colorama==0.4.2")?;

    uv_snapshot!(context.filters(), windows_filters=false, command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + colorama==0.4.2
    warning: colorama==0.4.2 is yanked (reason: "Bad build, missing files, will not install"). Refresh your lockfile to pin an un-yanked version.
    "###
    );

    Ok(())
}

/// Resolve a local wheel.
#[test]
fn install_local_wheel() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a wheel.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/97/75/10a9ebee3fd790d20926a90a2547f0bf78f371b2f13aa822c759680ca7b9/tomli-2.0.1-py3-none-any.whl")?;
    let archive = context.temp_dir.child("tomli-2.0.1-py3-none-any.whl");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tomli @ {}",
        Url::from_file_path(archive.path()).unwrap()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tomli").success();

    // Create a new virtual environment.
    let venv = create_venv(&context.temp_dir, &context.cache_dir, "3.12");

    // Reinstall. The wheel should come from the cache, so there shouldn't be a "download".
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tomli").success();

    // Create a new virtual environment.
    let venv = create_venv(&context.temp_dir, &context.cache_dir, "3.12");

    // "Modify" the wheel.
    // The `filetime` crate works on Windows unlike the std.
    filetime::set_file_mtime(&archive, filetime::FileTime::now()).unwrap();

    // Reinstall. The wheel should be "downloaded" again.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tomli").success();

    // "Modify" the wheel.
    filetime::set_file_mtime(&archive, filetime::FileTime::now()).unwrap();

    // Reinstall into the same virtual environment. The wheel should be reinstalled.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tomli").success();

    Ok(())
}

/// Install a wheel whose actual version doesn't match the version encoded in the filename.
#[test]
fn mismatched_version() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a wheel.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/97/75/10a9ebee3fd790d20926a90a2547f0bf78f371b2f13aa822c759680ca7b9/tomli-2.0.1-py3-none-any.whl")?;
    let archive = context.temp_dir.child("tomli-3.7.2-py3-none-any.whl");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tomli @ {}",
        Url::from_file_path(archive.path()).unwrap()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    error: Failed to install: tomli-3.7.2-py3-none-any.whl (tomli==3.7.2 (from file://[TEMP_DIR]/tomli-3.7.2-py3-none-any.whl))
      Caused by: Wheel version does not match filename: 2.0.1 != 3.7.2
    "###
    );

    Ok(())
}

/// Install a wheel whose actual name doesn't match the name encoded in the filename.
#[test]
fn mismatched_name() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a wheel.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/97/75/10a9ebee3fd790d20926a90a2547f0bf78f371b2f13aa822c759680ca7b9/tomli-2.0.1-py3-none-any.whl")?;
    let archive = context.temp_dir.child("foo-2.0.1-py3-none-any.whl");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "foo @ {}",
        Url::from_file_path(archive.path()).unwrap()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because foo has an invalid package format and you require foo, we can conclude that the requirements are unsatisfiable.

          hint: The structure of foo was invalid:
            The .dist-info directory tomli-2.0.1 does not start with the normalized package name: foo
    "###
    );

    Ok(())
}

/// Install a local source distribution.
#[test]
fn install_local_source_distribution() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a source distribution.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/b0/b4/bc2baae3970c282fae6c2cb8e0f179923dceb7eaffb0e76170628f9af97b/wheel-0.42.0.tar.gz")?;
    let archive = context.temp_dir.child("wheel-0.42.0.tar.gz");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "wheel @ {}",
        Url::from_file_path(archive.path()).unwrap()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + wheel==0.42.0 (from file://[TEMP_DIR]/wheel-0.42.0.tar.gz)
    "###
    );

    context.assert_command("import wheel").success();

    Ok(())
}

/// The `ujson` package includes a `[build-system]`, but no `build-backend`. It lists some explicit
/// build requirements, but _also_ depends on `wheel` and `setuptools`:
/// ```toml
/// [build-system]
/// requires = ["setuptools>=42", "setuptools_scm[toml]>=3.4"]
/// ```
///
/// Like `pip` and `build`, we should use PEP 517 here and respect the `requires`, but use the
/// default build backend.
#[test]
#[cfg(unix)] // https://github.com/astral-sh/uv/issues/1238
fn install_ujson() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("ujson @ https://files.pythonhosted.org/packages/43/1a/b0a027144aa5c8f4ea654f4afdd634578b450807bb70b9f8bad00d6f6d3c/ujson-5.7.0.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + ujson==5.7.0 (from https://files.pythonhosted.org/packages/43/1a/b0a027144aa5c8f4ea654f4afdd634578b450807bb70b9f8bad00d6f6d3c/ujson-5.7.0.tar.gz)
    "###
    );

    context.assert_command("import ujson").success();

    Ok(())
}

/// This package includes a `[build-system]`, but no `build-backend`.
///
/// It lists some explicit build requirements that are necessary to build the distribution:
/// ```toml
/// [build-system]
/// requires = ["Cython<3", "setuptools", "wheel"]
/// ```
///
/// Like `pip` and `build`, we should use PEP 517 here and respect the `requires`, but use the
/// default build backend.
///
/// The example is based `DTLSSocket==0.1.16`
#[test]
fn install_build_system_no_backend() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("build-system-no-backend @ https://files.pythonhosted.org/packages/ec/25/1e531108ca027dc3a3b37d351f4b86d811df4884c6a81cd99e73b8b589f5/build-system-no-backend-0.1.0.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + build-system-no-backend==0.1.0 (from https://files.pythonhosted.org/packages/ec/25/1e531108ca027dc3a3b37d351f4b86d811df4884c6a81cd99e73b8b589f5/build-system-no-backend-0.1.0.tar.gz)
    "###
    );

    context
        .assert_command("import build_system_no_backend")
        .success();

    Ok(())
}

/// Check that we show the right messages on cached, direct URL source distribution installs.
#[test]
fn install_url_source_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tqdm @ https://files.pythonhosted.org/packages/62/06/d5604a70d160f6a6ca5fd2ba25597c24abd5c5ca5f437263d177ac242308/tqdm-4.66.1.tar.gz")?;

    let filters = if cfg!(windows) {
        [("warning: The package `tqdm` requires `colorama ; platform_system == 'Windows'`, but it's not installed.\n", "")]
            .into_iter()
            .chain(context.filters())
            .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/62/06/d5604a70d160f6a6ca5fd2ba25597c24abd5c5ca5f437263d177ac242308/tqdm-4.66.1.tar.gz)
    "###
    );

    context.assert_command("import tqdm").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/62/06/d5604a70d160f6a6ca5fd2ba25597c24abd5c5ca5f437263d177ac242308/tqdm-4.66.1.tar.gz)
    "###
    );

    context.assert_command("import tqdm").success();

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(Command::new(get_bin())
        .arg("clean")
        .arg("tqdm")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 126 files for tqdm ([SIZE])
    "###
    );

    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/62/06/d5604a70d160f6a6ca5fd2ba25597c24abd5c5ca5f437263d177ac242308/tqdm-4.66.1.tar.gz)
    "###
    );

    context.assert_command("import tqdm").success();

    Ok(())
}

/// Check that we show the right messages on cached, Git source distribution installs.
#[test]
#[cfg(feature = "git")]
fn install_git_source_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    check_command(&venv, "import werkzeug", &context.temp_dir);

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    let filters = if cfg!(windows) {
        [("Removed 2 files", "Removed 3 files")]
            .into_iter()
            .chain(context.filters())
            .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, Command::new(get_bin())
        .arg("clean")
        .arg("werkzeug")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 3 files for werkzeug ([SIZE])
    "###
    );

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Check that we show the right messages on cached, registry source distribution installs.
#[test]
fn install_registry_source_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("future==0.18.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + future==0.18.3
    "###
    );

    context.assert_command("import future").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + future==0.18.3
    "###
    );

    context.assert_command("import future").success();

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    let filters = if cfg!(windows) {
        [("Removed 615 files", "Removed 616 files")]
            .into_iter()
            .chain(context.filters())
            .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, Command::new(get_bin())
        .arg("clean")
        .arg("future")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 616 files for future ([SIZE])
    "###
    );

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + future==0.18.3
    "###
    );

    context.assert_command("import future").success();

    Ok(())
}

/// Check that we show the right messages on cached, local source distribution installs.
#[test]
fn install_path_source_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a source distribution.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/b0/b4/bc2baae3970c282fae6c2cb8e0f179923dceb7eaffb0e76170628f9af97b/wheel-0.42.0.tar.gz")?;
    let archive = context.temp_dir.child("wheel-0.42.0.tar.gz");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "wheel @ {}",
        Url::from_file_path(archive.path()).unwrap()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + wheel==0.42.0 (from file://[TEMP_DIR]/wheel-0.42.0.tar.gz)
    "###
    );

    context.assert_command("import wheel").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + wheel==0.42.0 (from file://[TEMP_DIR]/wheel-0.42.0.tar.gz)
    "###
    );

    context.assert_command("import wheel").success();

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    let filters = if cfg!(windows) {
        [("Removed 3 files", "Removed 4 files")]
            .into_iter()
            .chain(context.filters())
            .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, Command::new(get_bin())
        .arg("clean")
        .arg("wheel")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 102 files for wheel ([SIZE])
    "###
    );

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + wheel==0.42.0 (from file://[TEMP_DIR]/wheel-0.42.0.tar.gz)
    "###
    );

    context.assert_command("import wheel").success();

    Ok(())
}

/// Check that we show the right messages on cached, local source distribution installs.
#[test]
fn install_path_built_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    // Download a wheel.
    let response = reqwest::blocking::get("https://files.pythonhosted.org/packages/97/75/10a9ebee3fd790d20926a90a2547f0bf78f371b2f13aa822c759680ca7b9/tomli-2.0.1-py3-none-any.whl")?;
    let archive = context.temp_dir.child("tomli-2.0.1-py3-none-any.whl");
    let mut archive_file = fs_err::File::create(archive.path())?;
    std::io::copy(&mut response.bytes()?.as_ref(), &mut archive_file)?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    let url = Url::from_file_path(archive.path()).unwrap();
    requirements_txt.write_str(&format!("tomli @ {url}"))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tomli").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&context.temp_dir, &context.cache_dir, "3.12");

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    check_command(&venv, "import tomli", &parent);

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    let filters = if cfg!(windows) {
        // We do not display sizes on Windows
        [(
            "Removed 1 file for tomli",
            "Removed 1 file for tomli ([SIZE])",
        )]
        .into_iter()
        .chain(context.filters())
        .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, Command::new(get_bin())
        .arg("clean")
        .arg("tomli")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 2 files for tomli ([SIZE])
    "###
    );

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from file://[TEMP_DIR]/tomli-2.0.1-py3-none-any.whl)
    "###
    );

    check_command(&venv, "import tomli", &context.temp_dir);

    Ok(())
}

/// Check that we show the right messages on cached, direct URL built distribution installs.
#[test]
fn install_url_built_dist_cached() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tqdm @ https://files.pythonhosted.org/packages/00/e5/f12a80907d0884e6dff9c16d0c0114d81b8cd07dc3ae54c5e962cc83037e/tqdm-4.66.1-py3-none-any.whl")?;

    let filters = if cfg!(windows) {
        [("warning: The package `tqdm` requires `colorama ; platform_system == 'Windows'`, but it's not installed.\n", "")]
            .into_iter()
            .chain(context.filters())
            .collect()
    } else {
        context.filters()
    };
    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/00/e5/f12a80907d0884e6dff9c16d0c0114d81b8cd07dc3ae54c5e962cc83037e/tqdm-4.66.1-py3-none-any.whl)
    "###
    );

    context.assert_command("import tqdm").success();

    // Re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/00/e5/f12a80907d0884e6dff9c16d0c0114d81b8cd07dc3ae54c5e962cc83037e/tqdm-4.66.1-py3-none-any.whl)
    "###
    );

    check_command(&venv, "import tqdm", &context.temp_dir);

    // Clear the cache, then re-run the installation in a new virtual environment.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(Command::new(get_bin())
        .arg("clean")
        .arg("tqdm")
        .arg("--cache-dir")
        .arg(context.cache_dir.path())
        .env("VIRTUAL_ENV", venv.as_os_str())
        .current_dir(&context.temp_dir), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Removed 3 files for tqdm ([SIZE])
    "###
    );

    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==4.66.1 (from https://files.pythonhosted.org/packages/00/e5/f12a80907d0884e6dff9c16d0c0114d81b8cd07dc3ae54c5e962cc83037e/tqdm-4.66.1-py3-none-any.whl)
    "###
    );

    check_command(&venv, "import tqdm", &context.temp_dir);

    Ok(())
}

/// Verify that fail with an appropriate error when a package is repeated.
#[test]
fn duplicate_package_overlap() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\nMarkupSafe==2.1.2")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to determine installation plan
      Caused by: Detected duplicate package in requirements: markupsafe
    "###
    );

    Ok(())
}

/// Verify that allow duplicate packages when they are disjoint.
#[test]
fn duplicate_package_disjoint() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\nMarkupSafe==2.1.2 ; python_version < '3.6'")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + markupsafe==2.1.3
    "###
    );

    Ok(())
}

/// Verify that we can force reinstall of packages.
#[test]
fn reinstall() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    // Re-run the installation with `--reinstall`.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 2 packages in [TIME]
    Installed 2 packages in [TIME]
     - markupsafe==2.1.3
     + markupsafe==2.1.3
     - tomli==2.0.1
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    Ok(())
}

/// Verify that we can force reinstall of selective packages.
#[test]
fn reinstall_package() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    // Re-run the installation with `--reinstall`.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall-package")
        .arg("tomli")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - tomli==2.0.1
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    Ok(())
}

/// Verify that we can force reinstall of Git dependencies.
#[test]
#[cfg(feature = "git")]
fn reinstall_git() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("werkzeug @ git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    // Re-run the installation with `--reinstall`.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall-package")
        .arg("WerkZeug")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
     + werkzeug==2.0.0 (from git+https://github.com/pallets/werkzeug.git@af160e0b6b7ddd81c22f1652c728ff5ac72d5c74)
    "###
    );

    context.assert_command("import werkzeug").success();

    Ok(())
}

/// Verify that we can force refresh of cached data.
#[test]
fn refresh() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    // Re-run the installation into with `--refresh`. Ensure that we resolve and download the
    // latest versions of the packages.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    check_command(&venv, "import markupsafe", &context.temp_dir);
    check_command(&venv, "import tomli", &context.temp_dir);

    Ok(())
}

/// Verify that we can force refresh of selective packages.
#[test]
fn refresh_package() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3\ntomli==2.0.1")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    // Re-run the installation into with `--refresh`. Ensure that we resolve and download the
    // latest versions of the packages.
    let parent = context.temp_dir.child("parent");
    parent.create_dir_all()?;
    let venv = create_venv(&parent, &context.cache_dir, "3.12");

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh-package")
        .arg("tomli")
        .arg("--strict")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 2 packages in [TIME]
     + markupsafe==2.1.3
     + tomli==2.0.1
    "###
    );

    context.assert_command("import markupsafe").success();
    context.assert_command("import tomli").success();

    Ok(())
}

#[test]
#[cfg(feature = "maturin")]
fn sync_editable() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&indoc::formatdoc! {r"
        boltons==23.1.1
        -e {workspace_root}/scripts/packages/maturin_editable
        numpy==1.26.2
            # via poetry-editable
        -e file://{workspace_root}/scripts/packages/poetry_editable
        ",
        workspace_root = context.workspace_root.simplified_display(),
    })?;

    // Install the editable packages.
    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 2 editables in [TIME]
    Resolved 2 packages in [TIME]
    Downloaded 2 packages in [TIME]
    Installed 4 packages in [TIME]
     + boltons==23.1.1
     + maturin-editable==0.1.0 (from file://[WORKSPACE]/scripts/packages/maturin_editable)
     + numpy==1.26.2
     + poetry-editable==0.1.0 (from file://[WORKSPACE]/scripts/packages/poetry_editable)
    "###
    );

    // Reinstall the editable packages.
    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path())
        .arg("--reinstall-package")
        .arg("poetry-editable"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 1 editable in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - poetry-editable==0.1.0 (from file://[WORKSPACE]/scripts/packages/poetry_editable)
     + poetry-editable==0.1.0 (from file://[WORKSPACE]/scripts/packages/poetry_editable)
    "###
    );

    // Make sure we have the right base case.
    let python_source_file = context
        .workspace_root
        .join("scripts/packages/maturin_editable/python/maturin_editable/__init__.py");
    let python_version_1 = indoc::indoc! {r"
        from .maturin_editable import *

        version = 1
   "};
    fs_err::write(&python_source_file, python_version_1)?;

    let check_installed = indoc::indoc! {r#"
        from maturin_editable import sum_as_string, version

        assert version == 1, version
        assert sum_as_string(1, 2) == "3", sum_as_string(1, 2)
   "#};
    context.assert_command(check_installed).success();

    // Edit the sources.
    let python_version_2 = indoc::indoc! {r"
        from .maturin_editable import *

        version = 2
   "};
    fs_err::write(&python_source_file, python_version_2)?;

    let check_installed = indoc::indoc! {r#"
        from maturin_editable import sum_as_string, version
        from pathlib import Path

        assert version == 2, version
        assert sum_as_string(1, 2) == "3", sum_as_string(1, 2)
   "#};
    context.assert_command(check_installed).success();

    // Don't create a git diff.
    fs_err::write(&python_source_file, python_version_1)?;

    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 4 packages in [TIME]
    "###
    );

    Ok(())
}

#[test]
fn sync_editable_and_registry() -> Result<()> {
    let context = TestContext::new("3.12");

    // Copy the black test editable into the "current" directory
    copy_dir_all(
        context
            .workspace_root
            .join("scripts/packages/black_editable"),
        context.temp_dir.join("black_editable"),
    )?;

    // Install the registry-based version of Black.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc::indoc! {r"
        black==24.1.0
        "
    })?;

    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path())
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + black==24.1.0
    warning: The package `black` requires `click>=8.0.0`, but it's not installed.
    warning: The package `black` requires `mypy-extensions>=0.4.3`, but it's not installed.
    warning: The package `black` requires `packaging>=22.0`, but it's not installed.
    warning: The package `black` requires `pathspec>=0.9.0`, but it's not installed.
    warning: The package `black` requires `platformdirs>=2`, but it's not installed.
    "###
    );

    // Install the editable version of Black. This should remove the registry-based version.
    // Use the `file:` syntax for extra coverage.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc::indoc! {r"
        -e file:./black_editable
        "
    })?;

    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 1 editable in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - black==24.1.0
     + black==0.1.0 (from file://[TEMP_DIR]/black_editable)
    "###
    );

    // Re-install the registry-based version of Black. This should be a no-op, since we have a
    // version of Black installed (the editable version) that satisfies the requirements.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc::indoc! {r"
        black
        "
    })?;

    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 1 package in [TIME]
    "###
    );

    // Re-install Black at a specific version. This should replace the editable version.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc::indoc! {r"
        black==23.10.0
        "
    })?;

    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path())
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - black==0.1.0 (from file://[TEMP_DIR]/black_editable)
     + black==23.10.0
    warning: The package `black` requires `click>=8.0.0`, but it's not installed.
    warning: The package `black` requires `mypy-extensions>=0.4.3`, but it's not installed.
    warning: The package `black` requires `packaging>=22.0`, but it's not installed.
    warning: The package `black` requires `pathspec>=0.9.0`, but it's not installed.
    warning: The package `black` requires `platformdirs>=2`, but it's not installed.
    "###
    );

    Ok(())
}

#[test]
fn incompatible_wheel() -> Result<()> {
    let context = TestContext::new("3.12");
    let wheel = context.temp_dir.child("foo-1.2.3-not-compatible-wheel.whl");
    wheel.touch()?;

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!("foo @ {}", wheel.path().simplified_display()))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--strict"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to determine installation plan
      Caused by: A path dependency is incompatible with the current platform: foo-1.2.3-not-compatible-wheel.whl
    "###
    );

    Ok(())
}

/// Install a project without a `pyproject.toml`, using the PEP 517 build backend (default).
#[test]
fn sync_legacy_sdist_pep_517() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("flake8 @ https://files.pythonhosted.org/packages/66/53/3ad4a3b74d609b3b9008a10075c40e7c8909eae60af53623c3888f7a529a/flake8-6.0.0.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + flake8==6.0.0 (from https://files.pythonhosted.org/packages/66/53/3ad4a3b74d609b3b9008a10075c40e7c8909eae60af53623c3888f7a529a/flake8-6.0.0.tar.gz)
    "###
    );

    Ok(())
}

/// Install a project without a `pyproject.toml`, using `setuptools` directly.
#[test]
fn sync_legacy_sdist_setuptools() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("flake8 @ https://files.pythonhosted.org/packages/66/53/3ad4a3b74d609b3b9008a10075c40e7c8909eae60af53623c3888f7a529a/flake8-6.0.0.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.in")
        .arg("--legacy-setup-py"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + flake8==6.0.0 (from https://files.pythonhosted.org/packages/66/53/3ad4a3b74d609b3b9008a10075c40e7c8909eae60af53623c3888f7a529a/flake8-6.0.0.tar.gz)
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with a local directory.
#[test]
fn find_links() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        markupsafe==2.1.3
        numpy==1.26.3
        tqdm==1000.0.0
        werkzeug @ https://files.pythonhosted.org/packages/c3/fc/254c3e9b5feb89ff5b9076a23218dafbc99c96ac5941e900b71206e6313b/werkzeug-3.0.1-py3-none-any.whl
    "})?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 4 packages in [TIME]
    Downloaded 4 packages in [TIME]
    Installed 4 packages in [TIME]
     + markupsafe==2.1.3
     + numpy==1.26.3
     + tqdm==1000.0.0
     + werkzeug==3.0.1 (from https://files.pythonhosted.org/packages/c3/fc/254c3e9b5feb89ff5b9076a23218dafbc99c96ac5941e900b71206e6313b/werkzeug-3.0.1-py3-none-any.whl)
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with `--no-index`, which should accept the local wheel.
#[test]
fn find_links_no_index_match() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        tqdm==1000.0.0
    "})?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--no-index")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==1000.0.0
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with `--offline`, which should accept the local wheel.
#[test]
fn find_links_offline_match() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        tqdm==1000.0.0
    "})?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--offline")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==1000.0.0
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with `--offline`, which should fail to find `numpy`.
#[test]
fn find_links_offline_no_match() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        numpy
        tqdm==1000.0.0
    "})?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--offline")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because numpy was not found in the cache and you require numpy, we can conclude that the requirements are unsatisfiable.

          hint: Packages were unavailable because the network was disabled
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with a local directory. Ensure that cached wheels are reused.
#[test]
fn find_links_wheel_cache() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        tqdm==1000.0.0
    "})?;

    // Install `tqdm`.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==1000.0.0
    "###
    );

    // Reinstall `tqdm` with `--reinstall`. Ensure that the wheel is reused.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - tqdm==1000.0.0
     + tqdm==1000.0.0
    "###
    );

    Ok(())
}

/// Sync using `--find-links` with a local directory. Ensure that cached source distributions are
/// reused.
#[test]
fn find_links_source_cache() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(indoc! {r"
        tqdm==999.0.0
    "})?;

    // Install `tqdm`.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==999.0.0
    "###
    );

    // Reinstall `tqdm` with `--reinstall`. Ensure that the wheel is reused.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--find-links")
        .arg(context.workspace_root.join("scripts/links/")), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - tqdm==999.0.0
     + tqdm==999.0.0
    "###
    );

    Ok(())
}

/// Install without network access via the `--offline` flag.
#[test]
fn offline() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("black==23.10.1")?;

    // Install with `--offline` with an empty cache.
    uv_snapshot!(command(&context)
        .arg("requirements.in")
        .arg("--offline"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because black==23.10.1 was not found in the cache and you require black==23.10.1, we can conclude that the requirements are unsatisfiable.

          hint: Packages were unavailable because the network was disabled
    "###
    );

    // Populate the cache.
    uv_snapshot!(command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + black==23.10.1
    "###
    );

    // Install with `--offline` with a populated cache.
    let venv = create_venv(&context.temp_dir, &context.cache_dir, "3.12");

    uv_snapshot!(command(&context)
        .arg("requirements.in")
        .arg("--offline")
        .env("VIRTUAL_ENV", venv.as_os_str()), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + black==23.10.1
    "###
    );

    Ok(())
}

/// Sync with a repeated `anyio` requirement. The second requirement should be ignored.
#[test]
fn repeat_requirement() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("anyio\nanyio")?;

    uv_snapshot!(command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.3.0
    "###);

    Ok(())
}

/// Sync with a repeated, but conflicting `anyio` requirement. The second requirement should cause
/// an error.
#[test]
fn conflicting_requirement() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("anyio\nanyio==4.0.0")?;

    uv_snapshot!(command(&context)
        .arg("requirements.in"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to determine installation plan
      Caused by: Detected duplicate package in requirements: anyio
    "###);

    Ok(())
}

/// Don't preserve the mtime from .tar.gz files, it may be the unix epoch (1970-01-01), while Python's zip
/// implementation can't handle files with an mtime older than 1980.
/// See also <https://github.com/alexcrichton/tar-rs/issues/349>.
#[test]
fn tar_dont_preserve_mtime() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("tomli @ https://files.pythonhosted.org/packages/c0/3f/d7af728f075fb08564c5949a9c95e44352e23dee646869fa104a3b2060a3/tomli-2.0.1.tar.gz")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tomli==2.0.1 (from https://files.pythonhosted.org/packages/c0/3f/d7af728f075fb08564c5949a9c95e44352e23dee646869fa104a3b2060a3/tomli-2.0.1.tar.gz)
    "###);

    Ok(())
}

/// Avoid creating a file with 000 permissions
#[test]
fn set_read_permissions() -> Result<()> {
    let context = TestContext::new("3.12");
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str("databricks==0.2")?;

    uv_snapshot!(command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + databricks==0.2
    "###);

    Ok(())
}

/// Test special case to generate versioned pip launchers.
/// <https://github.com/pypa/pip/blob/3898741e29b7279e7bffe044ecfbe20f6a438b1e/src/pip/_internal/operations/install/wheel.py#L283>
/// <https://github.com/astral-sh/uv/issues/1593>
#[test]
fn pip_entrypoints() -> Result<()> {
    let context = TestContext::new("3.12");

    // TODO(konstin): Remove git dep when the next pip version is released.
    for pip_requirement in ["pip==24.0", "pip @ git+https://github.com/pypa/pip"] {
        let requirements_txt = context.temp_dir.child("requirements.txt");
        requirements_txt.write_str(pip_requirement)?;

        command(&context)
            .arg("requirements.txt")
            .arg("--strict")
            .output()
            .expect("Failed to install pip");

        let bin_dir = context.venv.join(if cfg!(unix) {
            "bin"
        } else if cfg!(windows) {
            "Scripts"
        } else {
            unimplemented!("Only Windows and Unix are supported")
        });
        // Pip 24.0 contains a pip3.10 launcher.
        // https://inspector.pypi.io/project/pip/24.0/packages/8a/6a/19e9fe04fca059ccf770861c7d5721ab4c2aebc539889e97c7977528a53b/pip-24.0-py3-none-any.whl/pip-24.0.dist-info/entry_points.txt
        ChildPath::new(bin_dir.join(format!("pip3.10{EXE_SUFFIX}")))
            .assert(predicates::path::missing());
        ChildPath::new(bin_dir.join(format!("pip3.12{EXE_SUFFIX}")))
            .assert(predicates::path::exists());
    }

    Ok(())
}

#[test]
fn invalidate_on_change() -> Result<()> {
    let context = TestContext::new("3.12");

    // Create an editable package.
    let editable_dir = context.temp_dir.child("editable");
    editable_dir.create_dir_all()?;
    let pyproject_toml = editable_dir.child("pyproject.toml");
    pyproject_toml.write_str(
        r#"[project]
name = "example"
version = "0.0.0"
dependencies = [
  "anyio==4.0.0"
]
requires-python = ">=3.8"
"#,
    )?;

    // Write to a requirements file.
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str(&format!("-e {}", editable_dir.path().display()))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 1 editable in [TIME]
    Installed 1 package in [TIME]
     + example==0.0.0 (from file://[TEMP_DIR]/editable)
    "###
    );

    // Re-installing should be a no-op.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Audited 1 package in [TIME]
    "###
    );

    // Modify the editable package.
    pyproject_toml.write_str(
        r#"[project]
name = "example"
version = "0.0.0"
dependencies = [
  "anyio==3.7.1"
]
requires-python = ">=3.8"
"#,
    )?;

    // Re-installing should update the package.
    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.in"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 1 editable in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - example==0.0.0 (from file://[TEMP_DIR]/editable)
     + example==0.0.0 (from file://[TEMP_DIR]/editable)
    "###
    );

    Ok(())
}

/// Install with bytecode compilation.
#[test]
fn compile() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--compile")
        .arg("--strict"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
    Bytecode compiled 3 files in [TIME]
     + markupsafe==2.1.3
    "###
    );

    assert!(context
        .site_packages()
        .join("markupsafe")
        .join("__pycache__")
        .join("__init__.cpython-312.pyc")
        .exists());

    context.assert_command("import markupsafe").success();

    Ok(())
}

/// Test that the `PYC_INVALIDATION_MODE` option is recognized and that the error handling works.
#[test]
fn compile_invalid_pyc_invalidation_mode() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("MarkupSafe==2.1.3")?;

    let filters: Vec<_> = context
        .filters()
        .into_iter()
        .chain([
            // The first file can vary so we capture it here
            (
                r#"\[SITE_PACKAGES\].*\.py", received: "#,
                r#"[SITE_PACKAGES]/[FILE].py", received: "#,
            ),
        ])
        .collect();

    uv_snapshot!(filters, command(&context)
        .arg("requirements.txt")
        .arg("--compile")
        .arg("--strict")
        .env("PYC_INVALIDATION_MODE", "bogus"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
    error: Failed to bytecode-compile Python file in: [SITE_PACKAGES]/
      Caused by: Python process stderr:
    Invalid value for PYC_INVALIDATION_MODE "bogus", valid are "TIMESTAMP", "CHECKED_HASH", "UNCHECKED_HASH":
      Caused by: Bytecode compilation failed, expected "[SITE_PACKAGES]/[FILE].py", received: ""
    "###
    );

    Ok(())
}

/// Raise an error when an editable's `Requires-Python` constraint is not met.
#[test]
fn requires_python_editable() -> Result<()> {
    let context = TestContext::new("3.12");

    // Create an editable package with a `Requires-Python` constraint that is not met.
    let editable_dir = context.temp_dir.child("editable");
    editable_dir.create_dir_all()?;
    let pyproject_toml = editable_dir.child("pyproject.toml");
    pyproject_toml.write_str(
        r#"[project]
name = "example"
version = "0.0.0"
dependencies = [
  "anyio==4.0.0"
]
requires-python = "<=3.5"
"#,
    )?;

    // Write to a requirements file.
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str(&format!("-e {}", editable_dir.path().display()))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.in"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Editable `example` requires Python <=3.5, but 3.12.[X] is installed
    "###
    );

    Ok(())
}

/// Install packages from an index that "doesn't support" zip file streaming (by way of using
/// data descriptors).
#[test]
fn no_stream() -> Result<()> {
    let context = TestContext::new("3.12");

    // Write to a requirements file.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("hashb_foxglove_protocolbuffers_python==25.3.0.1.20240226043130+465630478360")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--index-url")
        .arg("https://buf.build/gen/python"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + hashb-foxglove-protocolbuffers-python==25.3.0.1.20240226043130+465630478360
    "###
    );

    Ok(())
}

/// Raise an error when a direct URL dependency's `Requires-Python` constraint is not met.
#[test]
fn requires_python_direct_url() -> Result<()> {
    let context = TestContext::new("3.12");

    // Create an editable package with a `Requires-Python` constraint that is not met.
    let editable_dir = context.temp_dir.child("editable");
    editable_dir.create_dir_all()?;
    let pyproject_toml = editable_dir.child("pyproject.toml");
    pyproject_toml.write_str(
        r#"[project]
name = "example"
version = "0.0.0"
dependencies = [
  "anyio==4.0.0"
]
requires-python = "<=3.5"
"#,
    )?;

    // Write to a requirements file.
    let requirements_in = context.temp_dir.child("requirements.in");
    requirements_in.write_str(&format!("example @ {}", editable_dir.path().display()))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.in"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because the current Python version (3.12.[X]) does not satisfy Python<=3.5 and example==0.0.0 depends on Python<=3.5, we can conclude that example==0.0.0 cannot be used.
          And because only example==0.0.0 is available and you require example, we can conclude that the requirements are unsatisfiable.
    "###
    );

    Ok(())
}

/// Use an unknown hash algorithm with `--require-hashes`.
#[test]
fn require_hashes_unknown_algorithm() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(
        "anyio==4.0.0 --hash=foo:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f",
    )?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Unsupported hash algorithm: `foo` (expected one of: `md5`, `sha256`, `sha384`, or `sha512`)
    "###
    );

    Ok(())
}

/// Omit the hash with `--require-hashes`.
#[test]
fn require_hashes_missing_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("anyio==4.0.0")?;

    // Install without error when `--require-hashes` is omitted.
    uv_snapshot!(command(&context)
        .arg("requirements.txt"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0
    "###
    );

    // Error when `--require-hashes` is provided.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: In `--require-hashes` mode, all requirement must have a hash, but none were provided for: anyio==4.0.0
    "###
    );

    Ok(())
}

/// Omit the version with `--require-hashes`.
#[test]
fn require_hashes_missing_version() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(
        "anyio --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f",
    )?;

    // Install without error when `--require-hashes` is omitted.
    uv_snapshot!(command(&context)
        .arg("requirements.txt"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.3.0
    "###
    );

    // Error when `--require-hashes` is provided.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: In `--require-hashes` mode, all requirement must have their versions pinned with `==`, but found: anyio
    "###
    );

    Ok(())
}

/// Use a non-`==` operator with `--require-hashes`.
#[test]
fn require_hashes_invalid_operator() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(
        "anyio>4.0.0 --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f",
    )?;

    // Install without error when `--require-hashes` is omitted.
    uv_snapshot!(command(&context)
        .arg("requirements.txt"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.3.0
    "###
    );

    // Error when `--require-hashes` is provided.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: In `--require-hashes` mode, all requirement must have their versions pinned with `==`, but found: anyio>4.0.0
    "###
    );

    Ok(())
}

/// Include the hash for _just_ the wheel with `--no-binary`.
#[test]
fn require_hashes_wheel_no_binary() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--no-binary")
        .arg(":all:")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio==4.0.0
      Caused by: Hash mismatch for anyio==4.0.0

    Expected:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a
    "###
    );

    Ok(())
}

/// Include the hash for _just_ the wheel with `--only-binary`.
#[test]
fn require_hashes_wheel_only_binary() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--only-binary")
        .arg(":all:")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0
    "###
    );

    Ok(())
}

/// Include the hash for _just_ the source distribution with `--no-binary`.
#[test]
fn require_hashes_source_no_binary() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--no-binary")
        .arg(":all:")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0
    "###
    );

    Ok(())
}

/// Include the hash for _just_ the source distribution, with `--binary-only`.
#[test]
fn require_hashes_source_only_binary() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--only-binary")
        .arg(":all:")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio==4.0.0
      Caused by: Hash mismatch for anyio==4.0.0

    Expected:
      sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a

    Computed:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    "###
    );

    Ok(())
}

/// Include the correct hash algorithm, but the wrong digest.
#[test]
fn require_hashes_wrong_digest() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio==4.0.0
      Caused by: Hash mismatch for anyio==4.0.0

    Expected:
      sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    "###
    );

    Ok(())
}

/// Include the correct hash, but the wrong algorithm.
#[test]
fn require_hashes_wrong_algorithm() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha512:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio==4.0.0
      Caused by: Hash mismatch for anyio==4.0.0

    Expected:
      sha512:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha512:f30761c1e8725b49c498273b90dba4b05c0fd157811994c806183062cb6647e773364ce45f0e1ff0b10e32fe6d0232ea5ad39476ccf37109d6b49603a09c11c2
    "###
    );

    Ok(())
}

/// Include the hash for a source distribution specified as a direct URL dependency.
#[test]
fn require_hashes_source_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz)
    "###
    );

    // Reinstall with the right hash, and verify that it's reused.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0 (from https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz)
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz)
    "###
    );

    // Reinstall with the wrong hash, and verify that it's rejected despite being cached.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz --hash=sha256:a7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to download and build: anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz
      Caused by: Hash mismatch for anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz

    Expected:
      sha256:a7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a

    Computed:
      sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a
    "###
    );

    Ok(())
}

/// Include the _wrong_ hash for a source distribution specified as a direct URL dependency.
#[test]
fn require_hashes_source_url_mismatch() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz --hash=sha256:a7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to download and build: anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz
      Caused by: Hash mismatch for anyio @ https://files.pythonhosted.org/packages/74/17/5075225ee1abbb93cd7fc30a2d343c6a3f5f71cf388f14768a7a38256581/anyio-4.0.0.tar.gz

    Expected:
      sha256:a7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a

    Computed:
      sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a
    "###
    );

    Ok(())
}

/// Include the hash for a built distribution specified as a direct URL dependency.
#[test]
fn require_hashes_wheel_url() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    // Reinstall with the right hash, and verify that it's reused.
    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    // Reinstall with the wrong hash, and verify that it's rejected despite being cached.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl
      Caused by: Hash mismatch for anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl

    Expected:
      sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    "###
    );

    // Sync a new dependency and include the wrong hash for anyio. Verify that we reuse anyio
    // despite the wrong hash, like pip, since we don't validate hashes for already-installed
    // distributions.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f\niniconfig==2.0.0 --hash=sha256:b6a85871a79d2e3b22d2d1b94ac2824226a63c6b741c88f7ae975f18b6778374")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + iniconfig==2.0.0
    "###
    );

    Ok(())
}

/// Include the _wrong_ hash for a built distribution specified as a direct URL dependency.
#[test]
fn require_hashes_wheel_url_mismatch() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl
      Caused by: Hash mismatch for anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl

    Expected:
      sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    "###
    );

    Ok(())
}

/// Reject Git dependencies when `--require-hashes` is provided.
#[test]
fn require_hashes_git() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio @ git+https://github.com/agronholm/anyio@4a23745badf5bf5ef7928f1e346e9986bd696d82 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to download and build: anyio @ git+https://github.com/agronholm/anyio@4a23745badf5bf5ef7928f1e346e9986bd696d82
      Caused by: Hash-checking is not supported for Git repositories: anyio @ git+https://github.com/agronholm/anyio@4a23745badf5bf5ef7928f1e346e9986bd696d82
    "###
    );

    Ok(())
}

/// Reject local directory dependencies when `--require-hashes` is provided.
#[test]
fn require_hashes_source_tree() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "black @ {} --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a",
        context
            .workspace_root
            .join("scripts/packages/black_editable")
            .display()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to build: black @ file://[WORKSPACE]/scripts/packages/black_editable
      Caused by: Hash-checking is not supported for local directories: black @ file://[WORKSPACE]/scripts/packages/black_editable
    "###
    );

    Ok(())
}

/// Include the hash for _just_ the wheel with `--only-binary`.
#[test]
fn require_hashes_re_download() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("anyio==4.0.0")?;

    // Install without `--require-hashes`.
    uv_snapshot!(command(&context)
        .arg("requirements.txt"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0
    "###
    );

    // Reinstall with `--require-hashes`, and the wrong hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio==4.0.0
      Caused by: Hash mismatch for anyio==4.0.0

    Expected:
      sha256:afdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    "###
    );

    // Reinstall with `--require-hashes`, and the right hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0
     + anyio==4.0.0
    "###
    );

    Ok(())
}

/// Include the hash for a built distribution specified as a local path dependency.
#[test]
fn require_hashes_wheel_path() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tqdm @ {} --hash=sha256:a34996d4bd5abb2336e14ff0a2d22b92cfd0f0ed344e6883041ce01953276a13",
        context
            .workspace_root
            .join("scripts/links/tqdm-1000.0.0-py3-none-any.whl")
            .display()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==1000.0.0 (from file://[WORKSPACE]/scripts/links/tqdm-1000.0.0-py3-none-any.whl)
    "###
    );

    Ok(())
}

/// Include the _wrong_ hash for a built distribution specified as a local path dependency.
#[test]
fn require_hashes_wheel_path_mismatch() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tqdm @ {} --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f",
        context
            .workspace_root
            .join("scripts/links/tqdm-1000.0.0-py3-none-any.whl")
            .display()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: tqdm @ file://[WORKSPACE]/scripts/links/tqdm-1000.0.0-py3-none-any.whl
      Caused by: Hash mismatch for tqdm @ file://[WORKSPACE]/scripts/links/tqdm-1000.0.0-py3-none-any.whl

    Expected:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:a34996d4bd5abb2336e14ff0a2d22b92cfd0f0ed344e6883041ce01953276a13
    "###
    );

    Ok(())
}

/// Include the hash for a source distribution specified as a local path dependency.
#[test]
fn require_hashes_source_path() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tqdm @ {} --hash=sha256:89fa05cffa7f457658373b85de302d24d0c205ceda2819a8739e324b75e9430b",
        context
            .workspace_root
            .join("scripts/links/tqdm-999.0.0.tar.gz")
            .display()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + tqdm==999.0.0 (from file://[WORKSPACE]/scripts/links/tqdm-999.0.0.tar.gz)
    "###
    );

    Ok(())
}

/// Include the _wrong_ hash for a source distribution specified as a local path dependency.
#[test]
fn require_hashes_source_path_mismatch() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&format!(
        "tqdm @ {} --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f",
        context
            .workspace_root
            .join("scripts/links/tqdm-999.0.0.tar.gz")
            .display()
    ))?;

    uv_snapshot!(context.filters(), command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to build: tqdm @ file://[WORKSPACE]/scripts/links/tqdm-999.0.0.tar.gz
      Caused by: Hash mismatch for tqdm @ file://[WORKSPACE]/scripts/links/tqdm-999.0.0.tar.gz

    Expected:
      sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f

    Computed:
      sha256:89fa05cffa7f457658373b85de302d24d0c205ceda2819a8739e324b75e9430b
    "###
    );

    Ok(())
}

/// We allow `--require-hashes` for direct URL dependencies.
#[test]
fn require_hashes_unnamed() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str(indoc::indoc! {r"
            https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
        "} )?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    Ok(())
}

/// We allow `--require-hashes` for editables, as long as no dependencies are included.
#[test]
fn require_hashes_editable() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str(&indoc::formatdoc! {r"
        -e file://{workspace_root}/scripts/packages/black_editable[d]
        ",
        workspace_root = context.workspace_root.simplified_display(),
    })?;

    // Install the editable packages.
    uv_snapshot!(context.filters(), command(&context)
        .arg(requirements_txt.path())
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Built 1 editable in [TIME]
    Installed 1 package in [TIME]
     + black==0.1.0 (from file://[WORKSPACE]/scripts/packages/black_editable)
    "###
    );

    Ok(())
}

/// If a dependency is repeated, the hash should be required for both instances.
#[test]
fn require_hashes_repeated_dependency() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a\nanyio")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: In `--require-hashes` mode, all requirement must have their versions pinned with `==`, but found: anyio
    "###
    );

    // Reverse the order.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio\nanyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: In `--require-hashes` mode, all requirement must have their versions pinned with `==`, but found: anyio
    "###
    );

    Ok(())
}

/// If a dependency is repeated, use the last hash provided. pip seems to use the _first_ hash.
#[test]
fn require_hashes_repeated_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    // Use the same hash in both cases.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str(indoc::indoc! { r"
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
    " })?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    // Use a different hash, but both are correct.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str(indoc::indoc! { r"
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:cfdb2b588b9fc25ede96d8db56ed50848b0b649dca3dd1df0b11f683bb9e0b5f
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha512:f30761c1e8725b49c498273b90dba4b05c0fd157811994c806183062cb6647e773364ce45f0e1ff0b10e32fe6d0232ea5ad39476ccf37109d6b49603a09c11c2
    " })?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--reinstall"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    // Use a different hash. The first hash is wrong, but that's fine, since we use the last hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str(indoc::indoc! { r"
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:a7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=md5:420d85e19168705cdf0223621b18831a
    " })?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--reinstall"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
     + anyio==4.0.0 (from https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl)
    "###
    );

    // Use a different hash. The second hash is wrong. This should fail, since we use the last hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str(indoc::indoc! { r"
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a
            anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl --hash=md5:520d85e19168705cdf0223621b18831a
    " })?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--reinstall"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl
      Caused by: Hash mismatch for anyio @ https://files.pythonhosted.org/packages/36/55/ad4de788d84a630656ece71059665e01ca793c04294c463fd84132f40fe6/anyio-4.0.0-py3-none-any.whl

    Expected:
      md5:520d85e19168705cdf0223621b18831a

    Computed:
      md5:420d85e19168705cdf0223621b18831a
    "###
    );

    Ok(())
}

/// If a dependency is repeated, the hash should be required for both instances.
#[test]
fn require_hashes_at_least_one() -> Result<()> {
    let context = TestContext::new("3.12");

    // Request `anyio` with a `sha256` hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + anyio==4.0.0
    "###
    );

    // Reinstall, requesting both `sha256` and `sha512`. We should reinstall from the cache, since
    // at least one hash matches.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a --hash=md5:420d85e19168705cdf0223621b18831a")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0
     + anyio==4.0.0
    "###
    );

    // This should be true even if the second hash is wrong.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("anyio==4.0.0 --hash=sha256:f7ed51751b2c2add651e5747c891b47e26d2a21be5d32d9311dfe9692f3e5d7a --hash=md5:1234")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - anyio==4.0.0
     + anyio==4.0.0
    "###
    );

    Ok(())
}

/// Using `--find-links`, but the registry doesn't provide us with a hash.
#[test]
fn require_hashes_find_links_no_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    // First, use the correct hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/no-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + example-a-961b4c22==1.0.0
    "###
    );

    // Second, use an incorrect hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("example-a-961b4c22==1.0.0 --hash=sha256:123")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/no-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:123

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Third, use the hash from the source distribution. This will actually fail, when it _could_
    // succeed, but pip has the same behavior.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:294e788dbe500fdc39e8b88e82652ab67409a1dc9dd06543d0fe0ae31b713eb3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/no-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:294e788dbe500fdc39e8b88e82652ab67409a1dc9dd06543d0fe0ae31b713eb3

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Fourth, use the hash from the source distribution, and disable wheels. This should succeed.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:294e788dbe500fdc39e8b88e82652ab67409a1dc9dd06543d0fe0ae31b713eb3")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--no-binary")
        .arg(":all:")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/no-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - example-a-961b4c22==1.0.0
     + example-a-961b4c22==1.0.0
    "###
    );

    Ok(())
}

/// Using `--find-links`, and the registry serves us a correct hash.
#[test]
fn require_hashes_find_links_valid_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/valid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + example-a-961b4c22==1.0.0
    "###
    );

    Ok(())
}

/// Using `--find-links`, and the registry serves us an incorrect hash.
#[test]
fn require_hashes_find_links_invalid_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    // First, request some other hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("example-a-961b4c22==1.0.0 --hash=sha256:123")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/invalid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:123

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Second, request the invalid hash, that the registry _thinks_ is correct. We should reject it.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:8838f9d005ff0432b258ba648d9cabb1cbdf06ac29d14f788b02edae544032ea")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/invalid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:8838f9d005ff0432b258ba648d9cabb1cbdf06ac29d14f788b02edae544032ea

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Third, request the correct hash, that the registry _thinks_ is correct. We should accept
    // it, since it's already cached under this hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/invalid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + example-a-961b4c22==1.0.0
    "###
    );

    // Fourth, request the correct hash, that the registry _thinks_ is correct, but without the
    // cache. We _should_ accept it, but we currently don't.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/invalid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - example-a-961b4c22==1.0.0
     + example-a-961b4c22==1.0.0
    "###
    );

    // Finally, request the correct hash, along with the incorrect hash for the source distribution.
    // Resolution will fail, since the incorrect hash matches the registry's hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e --hash=sha256:a3cf07a05aac526131a2e8b6e4375ee6c6eaac8add05b88035e960ac6cd999ee")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://raw.githubusercontent.com/astral-test/astral-test-hash/main/invalid-hash/simple-html/example-a-961b4c22/index.html"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to download and build: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
      sha256:a3cf07a05aac526131a2e8b6e4375ee6c6eaac8add05b88035e960ac6cd999ee

    Computed:
      sha256:294e788dbe500fdc39e8b88e82652ab67409a1dc9dd06543d0fe0ae31b713eb3
    "###
    );

    Ok(())
}

/// Using `--index-url`, but the registry doesn't provide us with a hash.
#[test]
fn require_hashes_registry_no_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/no-hash/simple-html/"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Installed 1 package in [TIME]
     + example-a-961b4c22==1.0.0
    "###
    );

    Ok(())
}

/// Using `--index-url`, and the registry serves us a correct hash.
#[test]
fn require_hashes_registry_valid_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--require-hashes")
        .arg("--find-links")
        .arg("https://astral-test.github.io/astral-test-hash/valid-hash/simple-html/"), @r###"
    success: false
    exit_code: 1
    ----- stdout -----

    ----- stderr -----
      × No solution found when resolving dependencies:
      ╰─▶ Because example-a-961b4c22==1.0.0 was not found in the package registry and you require example-a-961b4c22==1.0.0, we can conclude that the requirements are unsatisfiable.
    "###
    );

    Ok(())
}

/// Using `--index-url`, and the registry serves us an incorrect hash.
#[test]
fn require_hashes_registry_invalid_hash() -> Result<()> {
    let context = TestContext::new("3.12");

    // First, request some other hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt.write_str("example-a-961b4c22==1.0.0 --hash=sha256:123")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/invalid-hash/simple-html/"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:123

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Second, request the invalid hash, that the registry _thinks_ is correct. We should reject it.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:8838f9d005ff0432b258ba648d9cabb1cbdf06ac29d14f788b02edae544032ea")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/invalid-hash/simple-html/"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    error: Failed to download distributions
      Caused by: Failed to fetch wheel: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:8838f9d005ff0432b258ba648d9cabb1cbdf06ac29d14f788b02edae544032ea

    Computed:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
    "###
    );

    // Third, request the correct hash, that the registry _thinks_ is correct. We should accept
    // it, since it's already cached under this hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/invalid-hash/simple-html/"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Installed 1 package in [TIME]
     + example-a-961b4c22==1.0.0
    "###
    );

    // Fourth, request the correct hash, that the registry _thinks_ is correct, but without the
    // cache. We _should_ accept it, but we currently don't.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/invalid-hash/simple-html/"), @r###"
    success: true
    exit_code: 0
    ----- stdout -----

    ----- stderr -----
    Resolved 1 package in [TIME]
    Downloaded 1 package in [TIME]
    Uninstalled 1 package in [TIME]
    Installed 1 package in [TIME]
     - example-a-961b4c22==1.0.0
     + example-a-961b4c22==1.0.0
    "###
    );

    // Finally, request the correct hash, along with the incorrect hash for the source distribution.
    // Resolution will fail, since the incorrect hash matches the registry's hash.
    let requirements_txt = context.temp_dir.child("requirements.txt");
    requirements_txt
        .write_str("example-a-961b4c22==1.0.0 --hash=sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e --hash=sha256:a3cf07a05aac526131a2e8b6e4375ee6c6eaac8add05b88035e960ac6cd999ee")?;

    uv_snapshot!(command(&context)
        .arg("requirements.txt")
        .arg("--refresh")
        .arg("--reinstall")
        .arg("--require-hashes")
        .arg("--index-url")
        .arg("https://astral-test.github.io/astral-test-hash/invalid-hash/simple-html/"), @r###"
    success: false
    exit_code: 2
    ----- stdout -----

    ----- stderr -----
    error: Failed to download and build: example-a-961b4c22==1.0.0
      Caused by: Hash mismatch for example-a-961b4c22==1.0.0

    Expected:
      sha256:5d69f0b590514103234f0c3526563856f04d044d8d0ea1073a843ae429b3187e
      sha256:a3cf07a05aac526131a2e8b6e4375ee6c6eaac8add05b88035e960ac6cd999ee

    Computed:
      sha256:294e788dbe500fdc39e8b88e82652ab67409a1dc9dd06543d0fe0ae31b713eb3
    "###
    );

    Ok(())
}
