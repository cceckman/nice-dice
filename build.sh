#!/bin/sh

set -eu
wasm-pack build --target=web >&2

