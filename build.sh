#!/bin/sh

set -eux
wasm-pack build --target=web >&2

rm -rf dist/
mkdir -p dist/

rm pkg/.gitignore
cp -r pkg/ dist/
cp app.js dist/
cp demo.html dist/

CHARTS_VERSION="1.2.0"

curl -fL "https://github.com/ChartsCSS/charts.css/archive/refs/tags/${CHARTS_VERSION}.tar.gz" \
    -o charts.tar.gz
tar -xvf charts.tar.gz
cp charts.css-"${CHARTS_VERSION}"/dist/charts.min.css dist/charts.min.css

rm -rf ~/r/github.com/cceckman/web/static/writing/nice-dice/
cp -r dist ~/r/github.com/cceckman/web/static/writing/nice-dice
