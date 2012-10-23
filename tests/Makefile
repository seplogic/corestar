DIRS=$(wildcard *_tests)
DIRS_TEST=$(addsuffix .test,$(DIRS))
DIRS_CLEAN=$(addsuffix .clean,$(DIRS))

SHELL=/bin/bash

test: $(DIRS_TEST)
clean: $(DIRS_CLEAN)

$(DIRS_TEST): %.test:
	@echo -n "Testing $* "
	@$(MAKE) -s -C $* test
	@echo

$(DIRS_CLEAN): %.clean:
	$(MAKE) -C $* clean

.PHONY: test $(DIRS_TEST) clean $(DIRS_CLEAN)
.SILENT: test
