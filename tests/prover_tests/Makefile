TESTS=$(wildcard *_test)

SHELL=/bin/bash

test: $(TESTS)

$(TESTS): %_test:
	@"${CORESTAR_HOME}/bin/test_logic" -f $*_test -l $*_logic > $*.out 2> $*.err || echo -e "\nFailed $* in $(CURDIR) (see $*.out and $*.err)"

clean:
	rm -rf *.out *.err

.PHONY: test clean $(TESTS)
