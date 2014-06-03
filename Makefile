all:  build tags
.PHONY: all build install

build: dist/setup-config dist/build/hothasktags/hothasktags

dist/setup-config: hothasktags.cabal
	cabal install --only-dependencies
	cabal configure

dist/build/hothasktags/hothasktags: Main.hs
	cabal build

install: 
	cabal install

tags: build
	dist/build/hothasktags/hothasktags *.hs > tags
