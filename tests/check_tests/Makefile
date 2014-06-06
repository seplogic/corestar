TESTS=$(patsubst %.star,%.test,$(wildcard *.star))

SHELL=/bin/bash

test: $(TESTS)

clean:
	@rm -rf *.out

$(TESTS): %.test:
	@rm -rf $*.out && mkdir $*.out
	@echo "verifying $*.star"
	@cd $*.out;\
	  OCAMLRUNPARAM=b \
	  	corestar -v -v -v -noabd ../$*.star > stdout 2> stderr \
	  || echo "  $* gives exit code $$?"

.PHONY: test $(TESTS) clean
.SILENT: test
