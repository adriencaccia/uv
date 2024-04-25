use thiserror::Error;
use uv_cache::Cache;
use which::{which, which_all};

use crate::environment::python_environment::{
    detect_python_executable, virtualenv_from_env, virtualenv_from_working_dir,
};
use crate::selectors::ImplementationName;
use crate::Interpreter;
use std::borrow::Cow;
use std::io;
use std::num::ParseIntError;
use std::{path::PathBuf, str::FromStr};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PythonInterpreterRequest {
    /// A Python version without an implementation name
    Version(PythonVersionRequest),
    /// A path to a directory containing a Python installation
    Directory(PathBuf),
    /// A path to a Python executable
    File(PathBuf),
    /// The name of a Python executable
    ExecutableName(String),
    /// A Python implementation without a version
    Implementation(ImplementationName),
    /// A Python implementation name and version
    ImplementationVersion(ImplementationName, PythonVersionRequest),
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub(crate) enum PythonVersionRequest {
    #[default]
    Default,
    Major(u8),
    MajorMinor(u8, u8),
    MajorMinorPatch(u8, u8, u8),
}

#[derive(Clone, Debug)]
pub(crate) struct PythonInterpreterResult {
    source: PythonInterpreterSource,
    interpreter: Interpreter,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub(crate) enum PythonInterpreterSource {
    /// The interpreter path was provided directly
    ProvidedPath,
    /// The interpreter path was inherited from the parent process
    Parent,
    /// An environment was active e.g. via `VIRTUAL_ENV`
    ActiveEnvironment,
    /// An environment was discovered e.g. via `.venv`
    DiscoveredEnvironment,
    /// An executable was found in the `PATH`
    SearchPath,
    /// The interpreter was found in the uv toolchain directory
    ManagedToolchain,
}

#[derive(Error, Debug)]
pub(crate) enum PythonInterpreterError {
    #[error(transparent)]
    IOError(#[from] io::Error),
    #[error(transparent)]
    QueryError(#[from] crate::Error),
}

// Lazily iterate over all discoverable Python executables.
///
/// A [`PythonVersionRequest`] may be provided, adjusting the possible executable names.
fn python_executables<'a>(
    version: Option<&'a PythonVersionRequest>,
) -> Result<impl Iterator<Item = (PythonInterpreterSource, PathBuf)> + 'a, PythonInterpreterError> {
    let iter =
        // (1) The active environment
        virtualenv_from_env()?
        .into_iter()
        .map(|venv| detect_python_executable(venv))
        .map(|path| (PythonInterpreterSource::ActiveEnvironment, path))
        // (2) A discovered environment
        .chain(
            virtualenv_from_working_dir()?
            .into_iter()
            .map(|venv| detect_python_executable(venv))
            .map(|path| (PythonInterpreterSource::DiscoveredEnvironment, path))
        )
        // (3) The search path
        .chain(
            version
                .unwrap_or(&PythonVersionRequest::Default)
                .possible_names()
                .into_iter()
                .filter_map(|name| name)
                .filter_map(|name| which_all(name.into_owned()).ok())
                .flatten() // TODO(zanieb): Consider using `flatten_ok`
                .map(|path| (PythonInterpreterSource::SearchPath, path)),
        );
    // (4) The managed toolchains (TODO)

    Ok(iter)
}

// Lazily iterate over all discoverable Python interpreters.
///
/// A [`PythonVersionRequest`] may be provided, expanding the executable name search.
fn python_interpreters<'a>(
    version: Option<&'a PythonVersionRequest>,
    cache: &'a Cache,
) -> Result<impl Iterator<Item = (PythonInterpreterSource, Interpreter)> + 'a, PythonInterpreterError>
{
    let iter = python_executables(version)?.filter_map(|(source, path)| {
        if let Ok(interpreter) = Interpreter::query(path, cache) {
            Some((source, interpreter))
        } else {
            None
        }
    });

    Ok(iter)
}

impl PythonInterpreterRequest {
    pub(crate) fn find(
        &self,
        cache: &Cache,
    ) -> Result<Option<PythonInterpreterResult>, PythonInterpreterError> {
        let result = match self {
            Self::File(path) => {
                if !path.try_exists()? {
                    return Ok(None);
                }
                PythonInterpreterResult {
                    source: PythonInterpreterSource::ProvidedPath,
                    interpreter: Interpreter::query(path, cache)?,
                }
            }
            Self::Directory(path) => {
                if !path.try_exists()? {
                    return Ok(None);
                }
                // TODO: Search for the executable in the directory
                let executable = path;
                PythonInterpreterResult {
                    source: PythonInterpreterSource::ProvidedPath,
                    interpreter: Interpreter::query(executable, cache)?,
                }
            }
            Self::ExecutableName(name) => {
                let Some(executable) = which(name).ok() else {
                    return Ok(None);
                };
                PythonInterpreterResult {
                    source: PythonInterpreterSource::SearchPath,
                    interpreter: Interpreter::query(executable, cache)?,
                }
            }
            Self::Implementation(implementation) => {
                let Some((source, interpreter)) = python_interpreters(None, cache)?
                    .filter(|(_source, interpreter)| {
                        interpreter.implementation_name() == implementation.as_str()
                    })
                    .next()
                else {
                    return Ok(None);
                };
                PythonInterpreterResult {
                    source,
                    interpreter,
                }
            }
            Self::ImplementationVersion(implementation, version) => {
                let Some((source, interpreter)) = python_interpreters(Some(version), cache)?
                    .filter(|(_source, interpreter)| {
                        version.satisfied_by(interpreter)
                            && interpreter.implementation_name() == implementation.as_str()
                    })
                    .next()
                else {
                    return Ok(None);
                };
                PythonInterpreterResult {
                    source,
                    interpreter,
                }
            }
            Self::Version(version) => {
                let Some((source, interpreter)) = python_interpreters(Some(version), cache)?
                    .filter(|(_source, interpreter)| version.satisfied_by(interpreter))
                    .next()
                else {
                    return Ok(None);
                };
                PythonInterpreterResult {
                    source,
                    interpreter,
                }
            }
        };
        Ok(Some(result))
    }

    /// Create a request from a string.
    ///
    /// This cannot fail, which means weird inputs will be parsed as [`PythonInterpreterRequest::File`] or [`PythonInterpreterRequest::ExecutableName`].
    pub(crate) fn parse(value: &str) -> Self {
        // e.g. `3.12.1`
        if let Some(version) = PythonVersionRequest::from_str(value).ok() {
            return Self::Version(version);
        }
        // e.g. `python3.12.1`
        if let Some(remainder) = value.strip_prefix("python") {
            if let Some(version) = PythonVersionRequest::from_str(remainder).ok() {
                return Self::Version(version);
            }
        }
        // e.g. `pypy@3.12`
        if let Some((first, second)) = value.split_once("@") {
            if let Some(implementation) = ImplementationName::from_str(first).ok() {
                if let Some(version) = PythonVersionRequest::from_str(second).ok() {
                    return Self::ImplementationVersion(implementation.clone(), version);
                }
            }
        }
        for implementation in ImplementationName::iter() {
            if let Some(remainder) = value
                .to_ascii_lowercase()
                .strip_prefix(implementation.as_str())
            {
                // e.g. `pypy`
                if remainder.is_empty() {
                    return Self::Implementation(implementation.clone());
                }
                // e.g. `pypy3.12`
                if let Some(version) = PythonVersionRequest::from_str(remainder).ok() {
                    return Self::ImplementationVersion(implementation.clone(), version);
                }
            }
        }
        let value_as_path = PathBuf::from(value);
        // e.g. ./path/to/.venv
        if value_as_path.is_dir() {
            return Self::Directory(value_as_path);
        }
        // e.g. ./path/to/python3.exe
        // If it contains a path separator, we'll treat it as a full path even if it does not exist
        if value.contains(std::path::MAIN_SEPARATOR) {
            return Self::File(value_as_path);
        }
        // Finally, we'll treat it as the name of an executable (i.e. in the search PATH)
        // e.g. foo.exe
        return Self::ExecutableName(value.to_string());
    }
}

impl PythonVersionRequest {
    pub(crate) fn possible_names(self) -> [Option<Cow<'static, str>>; 4] {
        let (python, python3, extension) = if cfg!(windows) {
            (
                Cow::Borrowed("python.exe"),
                Cow::Borrowed("python3.exe"),
                ".exe",
            )
        } else {
            (Cow::Borrowed("python"), Cow::Borrowed("python3"), "")
        };

        match self {
            Self::Default => [Some(python3), Some(python), None, None],
            Self::Major(major) => [
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
                None,
                None,
            ],
            Self::MajorMinor(major, minor) => [
                Some(Cow::Owned(format!("python{major}.{minor}{extension}"))),
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
                None,
            ],
            Self::MajorMinorPatch(major, minor, patch) => [
                Some(Cow::Owned(format!(
                    "python{major}.{minor}.{patch}{extension}",
                ))),
                Some(Cow::Owned(format!("python{major}.{minor}{extension}"))),
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
            ],
        }
    }

    pub(crate) fn major(self) -> Option<u8> {
        match self {
            Self::Default => None,
            Self::Major(major) => Some(major),
            Self::MajorMinor(major, _) => Some(major),
            Self::MajorMinorPatch(major, _, _) => Some(major),
        }
    }

    /// Check if a interpreter matches the requested Python version.
    fn satisfied_by(&self, interpreter: &Interpreter) -> bool {
        match self {
            Self::Default => true,
            Self::Major(major) => interpreter.python_major() == *major,
            Self::MajorMinor(major, minor) => {
                (interpreter.python_major(), interpreter.python_minor()) == (*major, *minor)
            }
            Self::MajorMinorPatch(major, minor, patch) => {
                (
                    interpreter.python_major(),
                    interpreter.python_minor(),
                    interpreter.python_patch(),
                ) == (*major, *minor, *patch)
            }
        }
    }
}

impl FromStr for PythonVersionRequest {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let versions = s
            .splitn(3, '.')
            .map(str::parse::<u8>)
            .collect::<Result<Vec<_>, _>>()?;

        let selector = match versions.as_slice() {
            // e.g. `3`
            [major] => PythonVersionRequest::Major(*major),
            // e.g. `3.10`
            [major, minor] => PythonVersionRequest::MajorMinor(*major, *minor),
            // e.g. `3.10.4`
            [major, minor, patch] => PythonVersionRequest::MajorMinorPatch(*major, *minor, *patch),
            _ => unreachable!(),
        };

        Ok(selector)
    }
}

impl PythonInterpreterResult {
    #[allow(dead_code)]
    pub(crate) fn source(&self) -> &PythonInterpreterSource {
        &self.source
    }

    #[allow(dead_code)]
    pub(crate) fn interpreteter(&self) -> &Interpreter {
        &self.interpreter
    }

    pub(crate) fn into_interpreteter(self) -> Interpreter {
        self.interpreter
    }
}
#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::{
        request::{PythonInterpreterRequest, PythonVersionRequest},
        selectors::ImplementationName,
    };

    #[test]
    fn python_request_from_str() {
        assert_eq!(
            PythonInterpreterRequest::parse("3.12"),
            PythonInterpreterRequest::Version(PythonVersionRequest::from_str("3.12").unwrap())
        );
        assert_eq!(
            PythonInterpreterRequest::parse("foo"),
            PythonInterpreterRequest::ExecutableName("foo".to_string())
        );
        assert_eq!(
            PythonInterpreterRequest::parse("cpython"),
            PythonInterpreterRequest::Implementation(ImplementationName::Cpython)
        );
        assert_eq!(
            PythonInterpreterRequest::parse("cpython3.12.2"),
            PythonInterpreterRequest::ImplementationVersion(
                ImplementationName::Cpython,
                PythonVersionRequest::from_str("3.12.2").unwrap()
            )
        );
    }

    #[test]
    fn python_version_request_from_str() {
        assert_eq!(
            PythonVersionRequest::from_str("3"),
            Ok(PythonVersionRequest::Major(3))
        );
        assert_eq!(
            PythonVersionRequest::from_str("3.12"),
            Ok(PythonVersionRequest::MajorMinor(3, 12))
        );
        assert_eq!(
            PythonVersionRequest::from_str("3.12.1"),
            Ok(PythonVersionRequest::MajorMinorPatch(3, 12, 1))
        );
        assert!(PythonVersionRequest::from_str("1.foo.1").is_err());
    }
}
