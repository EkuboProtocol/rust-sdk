test:
    cargo test --features serde,evm,starknet

check:
    cargo check --features serde,evm,starknet
    cargo clippy --features evm,starknet,serde  --workspace -- -D warnings
    cargo fmt --check
