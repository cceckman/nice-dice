#!/bin/sh

set -eu
wasm-pack build --target=web >&2

cp -r pkg/ ~/r/github.com/cceckman/web/static/writing/nice-dice/
cp app.js ~/r/github.com/cceckman/web/static/writing/nice-dice/
cp demo.html ~/r/github.com/cceckman/web/static/writing/nice-dice/
mkdir -p ~/r/github.com/cceckman/web/static/writing/nice-dice/charts.css-1.1.0/dist
cp charts.css-1.1.0/dist/charts.min.css ~/r/github.com/cceckman/web/static/writing/nice-dice/charts.css-1.1.0/dist/charts.min.css
