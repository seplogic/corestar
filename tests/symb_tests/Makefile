TESTS=$(wildcard *_test)

SHELL=/bin/bash

test: $(TESTS)

$(TESTS): %_test:
	@"${CORESTAR_HOME}/bin/test_symb" -f $*_test -l $*_logic -a $*_abs > $*.out 2> $*.err || echo -e "\nFailed $* in $(CURDIR) (see $*.out and $*.err)"

clean:
	rm -f *.dot *proof_file*txt *.err *.out

.PHONY: test clean $(TESTS)
