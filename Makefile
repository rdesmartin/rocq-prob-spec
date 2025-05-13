# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS := --display=short

# --------------------------------------------------------------------
.PHONY: default build clean license

# --------------------------------------------------------------------
default: build
	@true

build:
	dune build $(DUNEOPTS)

clean:
	dune clean $(DUNEOPTS)
