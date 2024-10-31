.PHONY: codegen build test

build: src

test: build
	npx -c 'tree-sitter test'

node_modules:
	npm install

bindings binding.gyp Cargo.toml src: grammar.js node_modules
	npx -c 'tree-sitter generate'
	npx -c 'node-gyp configure'
	npx -c 'node-gyp build'

clean:
	rm -rf codegen bindings binding.gyp Cargo.toml src node_modules
