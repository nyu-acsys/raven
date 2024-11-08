.PHONY: codegen build test

build: tree-sitter-raven.so bindings.gyp

test: build
	tree-sitter test

Cargo.toml src: grammar.js
	tree-sitter generate
	tree-sitter build

tree-sitter-raven.so: Cargo.toml src
	cc -shared -fPIC -g -O3 -I src src/parser.c -o libtree-sitter-raven.so

bindings bindings.gyp node_modules:
	npm install

clean:
	rm -rf codegen bindings Cargo.toml Cargo.lock src node_modules *.so CMakeLists.txt go.mod target build Package.swift package-lock.json pyproject.toml setup.py log.html bindings binding.gyp
