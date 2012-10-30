TESTS=$(patsubst %.star,%.test,$(wildcard *.star))

SHELL=/bin/bash

test: $(TESTS)

clean:
	@rm -rf *.out

$(TESTS): %.test:
	@rm -rf $*.out && mkdir $*.out
	@cd $*.out; alt_abd -v -v -v ../$*.star > stdout 2> stderr; cd ..

.PHONY: test $(TESTS) clean
.SILENT: test
