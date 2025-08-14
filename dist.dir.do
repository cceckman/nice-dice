set -eu
wasm-pack build --target=web >&2

redo-ifchange charts.tar.gz

rm -rf dist/
mkdir -p dist/

rm pkg/.gitignore
cp -r pkg/ dist/
cp app.js dist/
cp demo.html dist/

tar -xvf charts.tar.gz
cp charts.css-*/dist/charts.min.css dist/charts.min.css

find dist/ -type f | xargs sha256sum
