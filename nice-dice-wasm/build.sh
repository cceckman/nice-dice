#!/bin/sh

set -eux
cargo component bindings
cargo component build --release

