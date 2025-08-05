#!/bin/sh

set -eux
cargo component bindings
cargo build --release

