# section that changes often

MAINS=corestar

# section that shouldn't change often

# wish there was an option to give to ocamlfind instead...
SHELL=/bin/bash
OCAMLBUILD=ocamlbuild -use-ocamlfind -cflag -annot -yaccflag -v
CPLN=scripts/_build/cpln.byte

build: native

native byte:
	@$(MAKE) -C scripts byte
	@$(OCAMLBUILD) $(addsuffix .$@,$(MAINS))
	@mkdir -p bin
	@for f in $(MAINS); do $(CPLN) $$f.$@ bin/$$f; rm $$f.$@; done

test: test-native

test-native test-byte: test-%: %
	$(MAKE) -s -C tests

doc:
	$(MAKE) -C doc/tutorial      		# DEV

scripts:
	$(MAKE) -C scripts			# DEV

all: build test

clean:
	ocamlbuild -clean
	rm -rf bin
	rm -f lib/*.a lib/* bin/* *.subdirs
	$(MAKE) -C tests clean
	$(MAKE) -C scripts clean       	# DEV
	$(MAKE) -C doc/tutorial clean  	# DEV

.PHONY: all build byte clean doc native scripts test test-byte test-native

-include .install.mk

#vim:noet:
