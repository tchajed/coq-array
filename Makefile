SRC_DIRS := 'src' $(shell test -d 'vendor' && echo 'vendor')
ALL_VFILES := $(shell find -L $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find -L 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find -L 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))

COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQARGS := $(COQPROJECT_ARGS)

default: $(VFILES:.v=.vo)
test: $(TEST_VFILES:.v=.vo) $(VFILES:.v=.vo)

.coqdeps.d: $(ALL_VFILES)
	@echo "COQDEP $@"
	@coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	@coqc $(COQARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob) .coqdeps.d
	@find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;

.PHONY: default test clean
.DELETE_ON_ERROR:
