.PHONY: codegen build test install_emacs

build: tree-sitter-raven.so bindings.gyp

test: build
	tree-sitter test

Cargo.toml src: grammar.js
	tree-sitter generate
	tree-sitter build

tree-sitter-raven.so: Cargo.toml src
	cc -shared -fPIC -g -O3 -I src src/parser.c -o libtree-sitter-raven.so

install_emacs: tree-sitter-raven.so
	cp ./libtree-sitter-raven.so ~/.emacs.d/tree-sitter/

bindings bindings.gyp node_modules:
	npm install

clean:
	rm -rf codegen bindings Cargo.toml Cargo.lock src node_modules *.so CMakeLists.txt go.mod target build Package.swift package-lock.json pyproject.toml setup.py log.html bindings binding.gyp
