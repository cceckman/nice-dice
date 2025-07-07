#!/bin/sh

set -eu
wasm-pack build --target=web >&2

cp -r pkg/ ~/r/github.com/cceckman/web/static/writing/dicer/
cp app.js ~/r/github.com/cceckman/web/static/writing/dicer/
cp demo.html ~/r/github.com/cceckman/web/static/writing/dicer/
mkdir -p ~/r/github.com/cceckman/web/static/writing/dicer/charts.css-1.1.0/dist
cp charts.css-1.1.0/dist/charts.min.css ~/r/github.com/cceckman/web/static/writing/dicer/charts.css-1.1.0/dist/charts.min.css
