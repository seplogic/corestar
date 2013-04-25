ML=infermli unused cpln
OFLAGS=-use-ocamlfind -cflag -dtypes

byte:
	ocamlbuild $(OFLAGS) $(addsuffix .byte,$(ML))

native:
	ocamlbuild $(OFLAGS) $(addsuffix .native,$(ML))

clean:
	ocamlbuild -clean

.PHONY: byte clean native
