check_tools:
	@echo "checking tools..."
	@command -v grcov >/dev/null || (echo "grcov is not installed" && exit 1)
	@command -v cargo >/dev/null || (echo "cargo is not installed" && exit 1)

run:
	./target/release/graph_viewer --file graph.tgf

cov: check_tools
	@echo "all tools are installed"
	CARGO_INCREMENTAL=0 RUSTFLAGS='-Cinstrument-coverage' LLVM_PROFILE_FILE='cargo-test-%p-%m.profraw' cargo test && \
	grcov . --binary-path ./target/debug/deps/ -s . -t html --branch --ignore-not-existing --ignore '../*' --ignore "/*" -o target/coverage/html && \
	rm cargo-test* && \
	rm default_*

test:
	cargo test -- --test-threads=4

r:
	cargo build -r -j4

doc:
	rustdoc ./src/*

doctest:
	cargo test --doc --package graph_project

cleanup:
	rm -rf doc && \
	rm -rf target

build: cleanup check_tools test doctest cov doc r
