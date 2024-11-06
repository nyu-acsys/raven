.PHONY: codegen build test

build: tree-sitter-raven.so

test: build
	npx -c 'tree-sitter test'

node_modules:
	npm install

bindings binding.gyp Cargo.toml src: grammar.js node_modules
	tree-sitter generate
	tree-sitter build

tree-sitter-raven.so: bindings binding.gyp Cargo.toml src
	cc -shared -fPIC -g -O3 -I src src/parser.c -o libtree-sitter-raven.so

clean:
	rm -rf codegen bindings binding.gyp Cargo.toml Cargo.lock src node_modules *.so CMakeLists.txt go.mod target build Package.swift package-lock.json pyproject.toml setup.py log.html
