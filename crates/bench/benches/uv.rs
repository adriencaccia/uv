use bench::criterion::black_box;
use bench::criterion::{criterion_group, criterion_main, measurement::WallTime, Criterion};
use distribution_types::Requirement;
use uv_cache::Cache;
use uv_client::RegistryClientBuilder;
use uv_interpreter::PythonEnvironment;
use uv_resolver::Manifest;

fn resolve_warm_jupyter(c: &mut Criterion<WallTime>) {
    let runtime = &tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();

    let cache = &Cache::from_path(".cache").unwrap().init().unwrap();
    let client = &RegistryClientBuilder::new(cache.clone()).build();
    let manifest = &Manifest::simple(vec![
        Requirement::from_pep508("jupyter".parse().unwrap()).unwrap()
    ]);

    let run = || {
        runtime
            .block_on(resolver::resolve(
                black_box(manifest.clone()),
                black_box(cache.clone()),
                black_box(client),
                None,
            ))
            .unwrap();
    };

    c.bench_function("resolve_warm_jupyter", |b| b.iter(run));
}

fn resolve_warm_airflow(c: &mut Criterion<WallTime>) {
    let runtime = &tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    let cache = &Cache::from_path(".cache").unwrap().init().unwrap();
    let venv = PythonEnvironment::from_default_python(cache).unwrap();
    let client = &RegistryClientBuilder::new(cache.clone()).build();
    let manifest = &Manifest::simple(vec![
        Requirement::from_pep508("apache-airflow[all]".parse().unwrap()).unwrap(),
        Requirement::from_pep508(
            "apache-airflow-providers-apache-beam>3.0.0"
                .parse()
                .unwrap(),
        )
        .unwrap(),
    ]);

    // install source distributions
    runtime
        .block_on(resolver::resolve(
            black_box(manifest.clone()),
            black_box(cache.clone()),
            black_box(client),
            Some(&venv),
        ))
        .unwrap();

    let run = || {
        runtime
            .block_on(resolver::resolve(
                black_box(manifest.clone()),
                black_box(cache.clone()),
                black_box(client),
                Some(&venv),
            ))
            .unwrap();
    };

    c.bench_function("resolve_warm_airflow", |b| b.iter(run));
}

criterion_group!(uv, resolve_warm_jupyter, resolve_warm_airflow);
criterion_main!(uv);

mod resolver {
    use anyhow::Result;
    use install_wheel_rs::linker::LinkMode;
    use once_cell::sync::Lazy;

    use distribution_types::IndexLocations;
    use pep508_rs::{MarkerEnvironment, MarkerEnvironmentBuilder};
    use platform_tags::{Arch, Os, Platform, Tags};
    use uv_cache::Cache;
    use uv_client::RegistryClient;
    use uv_configuration::{Concurrency, ConfigSettings, NoBinary, NoBuild, SetupPyStrategy};
    use uv_dispatch::BuildDispatch;
    use uv_distribution::DistributionDatabase;
    use uv_interpreter::{Interpreter, PythonEnvironment};
    use uv_resolver::{
        FlatIndex, InMemoryIndex, Manifest, Options, PythonRequirement, ResolutionGraph, Resolver,
    };
    use uv_types::{BuildIsolation, EmptyInstalledPackages, HashStrategy, InFlight};

    static MARKERS: Lazy<MarkerEnvironment> = Lazy::new(|| {
        MarkerEnvironment::try_from(MarkerEnvironmentBuilder {
            implementation_name: "cpython",
            implementation_version: "3.11.5",
            os_name: "posix",
            platform_machine: "arm64",
            platform_python_implementation: "CPython",
            platform_release: "21.6.0",
            platform_system: "Darwin",
            platform_version: "Darwin Kernel Version 21.6.0: Mon Aug 22 20:19:52 PDT 2022; root:xnu-8020.140.49~2/RELEASE_ARM64_T6000",
            python_full_version: "3.11.5",
            python_version: "3.11",
            sys_platform: "darwin",
        }).unwrap()
    });

    static PLATFORM: Platform = Platform::new(
        Os::Macos {
            major: 21,
            minor: 6,
        },
        Arch::Aarch64,
    );

    static TAGS: Lazy<Tags> =
        Lazy::new(|| Tags::from_env(&PLATFORM, (3, 11), "cpython", (3, 11), false).unwrap());

    pub(crate) async fn resolve(
        manifest: Manifest,
        cache: Cache,
        client: &RegistryClient,
        venv: Option<&PythonEnvironment>,
    ) -> Result<ResolutionGraph> {
        let interpreter = venv
            .as_ref()
            .map(|venv| venv.interpreter().clone())
            .unwrap_or_else(|| Interpreter::artificial(PLATFORM.clone(), MARKERS.clone()));

        let flat_index = FlatIndex::default();
        let index = InMemoryIndex::default();
        let hashes = HashStrategy::None;
        let index_locations = IndexLocations::default();
        let in_flight = InFlight::default();
        let installed_packages = EmptyInstalledPackages;
        let python_requirement = PythonRequirement::from_marker_environment(&interpreter, &MARKERS);
        let concurrency = Concurrency::default();
        let config_settings = ConfigSettings::default();
        let build_isolation = BuildIsolation::Isolated;

        let build_context = BuildDispatch::new(
            client,
            &cache,
            &interpreter,
            &index_locations,
            &flat_index,
            &index,
            &in_flight,
            SetupPyStrategy::default(),
            &config_settings,
            build_isolation,
            LinkMode::default(),
            &NoBuild::None,
            &NoBinary::None,
            concurrency,
        );

        let resolver = Resolver::new(
            manifest,
            Options::default(),
            &python_requirement,
            Some(&MARKERS),
            &TAGS,
            &flat_index,
            &index,
            &hashes,
            &build_context,
            installed_packages,
            DistributionDatabase::new(client, &build_context, concurrency.downloads),
        )?;

        Ok(resolver.resolve().await?)
    }
}
