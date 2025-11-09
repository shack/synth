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
	python3 termgen.py --terms $(1) --nodes $(2) --inputs $(3) --operators="-:1,~:1,&:2,|:2,+:2,--:2,<<:2,>>:2,*:2"
endef

$(eval $(call run-termgen,100,10,3))
$(eval $(call run-termgen,100,100,3))
PRECIOUS: $(terms)

rules :=
define get-rules
$(eval file := results/rule_gen/bv4-3vars-3iters-irr-enum-no-comp.json)
$(eval rules += $(ROOT)/$(file))
$(ROOT)/$(file):
	mkdir -p $(ROOT)/results/rule_gen
	@echo "Running bv4-3vars-3iters-irr-enum-no-comp"
	cd $(ROOT) && python3 rule_gen.py --mode bv --bitwidth 4 --vars 3 --max_length 3 --opt_level irr-enum --no-comp --no-norm
endef

$(eval $(call get-rules))
PRECIOUS: $(rules)

rewritten :=
define rewrite-terms # (file name)
$(eval file := terms/random/$(1).json)
$(eval rewritten-file := terms/random/$(1)-rewritten.json)
$(eval rewritten += $(ROOT)/$(rewritten-file))
$(ROOT)/$(rewritten-file): $(terms) $(rules)
	cd $(ROOT) && python3 rewriter.py --file $(ROOT)/$(file) --rulegen $(rules) --ruler $(ROOT)/results/ruler/bv4-3vars-3iters.json
endef

$(eval $(call rewrite-terms,random-3vars-10iters))
$(eval $(call rewrite-terms,random-3vars-100iters))
PRECIOUS: $(rewritten)

stats :=
define make-stats # (file name)
$(eval rewritten-file := terms/random/$(1)-rewritten.json)
$(eval stats-file := scripts/random_terms/$(1).pdf)
$(eval stats += $(ROOT)/$(stats-file))
$(ROOT)/$(stats-file): $(ROOT)/$(rewritten-file)
	python3 make_statistic.py --folder_path $(ROOT)/terms/random --separate
endef

$(eval $(call make-stats,random-3vars-10iters))
$(eval $(call make-stats,random-3vars-100iters))

.PHONY: terms
terms: $(terms)

.PHONY: rules
rules: $(rules)

.PHONY: rewrite
rewrite: $(rewritten)

.PHONY: stats
stats: $(stats)

.PHONY: clean
clean:
	rm -f $(rewritten) $(stats)

all: stats