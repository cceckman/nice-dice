set -eu

redo-ifchange Cargo.toml Cargo.lock app.js demo.html charts.min.css
find src -type f | xargs redo-ifchange

wasm-pack build --target=web >&2

rm -rf dist/
mkdir -p dist/

rm pkg/.gitignore
cp -r pkg/ dist/
cp app.js dist/
cp demo.html dist/

cp charts.css-*/dist/charts.min.css dist/charts.min.css

find dist/ -type f | xargs sha256sum
