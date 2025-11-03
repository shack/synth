SHELL=/usr/bin/env bash

all:

ROOT := $(abspath $(CURDIR)/../..)

terms :=

define run-termgen # (terms, nodes, inputs)
$(eval file := terms/random/random-$(3)vars-$(2)iters.json)
$(eval terms += $(ROOT)/$(file))
$(ROOT)/$(file): $(ROOT)/scripts/random_terms/termgen.py
	mkdir -p $(ROOT)/terms/random
	@echo "Generating $(1) terms of size $(2) nodes with $(3) inputs"
	python3 termgen.py --terms $(1) --nodes $(2) --inputs $(3) --operators="-:1,~:1,&:2,|:2,^:2,+:2,--:2,<<:2,>>:2,*:2"
endef

PRECIOUS: $(terms)

$(eval $(call run-termgen,100,100,3))

.PHONY: terms
terms: $(terms)

.PHONY: rewrite
rewrite: $(terms)
	python3 $(ROOT)/rewriter.py --folder_path $(ROOT)/terms/random --rule_file $(ROOT)/results/rule_gen/bv4-3vars-2iters-irr-enum.json

.PHONY: clean
clean:
	rm -f $(terms)

all: rewrite