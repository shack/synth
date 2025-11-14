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
$(eval file := results/rule_gen/bv4-3vars-3iters-irr-enum.json)
$(eval rules += $(ROOT)/$(file))
$(ROOT)/$(file):
	mkdir -p $(ROOT)/results/rule_gen
	@echo "Running bv4-3vars-3iters-irr-enum"
	cd $(ROOT) && python3 rule_gen.py --mode bv --bitwidth 4 --vars 3 --max_length 3 --opt_level irr-enum --no-norm
endef

$(eval $(call get-rules))
PRECIOUS: $(rules)

rewritten :=
define rewrite-terms # (file name, arg1, arg2, arg3, arg4, suffix)
$(eval file := terms/random/$(1).json)
$(eval rewritten-file := terms/random/$(1)-$(6).json)
$(eval rewritten += $(ROOT)/$(rewritten-file))
$(ROOT)/$(rewritten-file): $(terms) $(rules)
	cd $(ROOT) && python3 rewriter.py --file $(ROOT)/$(file) --rulegen $(rules) --ruler $(ROOT)/results/ruler/bv4-3vars-3iters.json $(2) $(3) $(4) $(5)
endef

$(eval $(call rewrite-terms,random-3vars-10iters,--set1_rulegen,--no-set1_egg,--set2_rulegen,--set2_egg,RuleGen_Greedy-RuleGen_Egglog))
$(eval $(call rewrite-terms,random-3vars-10iters,--set1_rulegen,--set1_egg,--no-set2_rulegen,--set2_egg,RuleGen_Egglog-Ruler_Egglog))
$(eval $(call rewrite-terms,random-3vars-10iters,--set1_rulegen,--no-set1_egg,--no-set2_rulegen,--no-set2_egg,RuleGen_Greedy-Ruler_Greedy))
$(eval $(call rewrite-terms,random-3vars-10iters,--set1_rulegen,--no-set1_egg,--no-set2_rulegen,--set2_egg,RuleGen_Greedy-Ruler_Egglog))

$(eval $(call rewrite-terms,random-3vars-100iters,--set1_rulegen,--no-set1_egg,--set2_rulegen,--set2_egg,RuleGen_Greedy-RuleGen_Egglog))
$(eval $(call rewrite-terms,random-3vars-100iters,--set1_rulegen,--set1_egg,--no-set2_rulegen,--set2_egg,RuleGen_Egglog-Ruler_Egglog))
$(eval $(call rewrite-terms,random-3vars-100iters,--set1_rulegen,--no-set1_egg,--no-set2_rulegen,--no-set2_egg,RuleGen_Greedy-Ruler_Greedy))
$(eval $(call rewrite-terms,random-3vars-100iters,--set1_rulegen,--no-set1_egg,--no-set2_rulegen,--set2_egg,RuleGen_Greedy-Ruler_Egglog))

PRECIOUS: $(rewritten)

stats :=
define make-stats # (file name, suffix)
$(eval rewritten-file := terms/random/$(1)-$(2).json)
$(eval stats-file := scripts/random_terms/$(1)-$(2).pdf)
$(eval stats += $(ROOT)/$(stats-file))
$(ROOT)/$(stats-file): $(ROOT)/$(rewritten-file)
	python3 make_statistic.py --file $(ROOT)/$(rewritten-file)
endef

$(eval $(call make-stats,random-3vars-10iters,RuleGen_Greedy-RuleGen_Egglog))
$(eval $(call make-stats,random-3vars-10iters,RuleGen_Egglog-Ruler_Egglog))
$(eval $(call make-stats,random-3vars-10iters,RuleGen_Greedy-Ruler_Greedy))
$(eval $(call make-stats,random-3vars-10iters,RuleGen_Greedy-Ruler_Egglog))

$(eval $(call make-stats,random-3vars-100iters,RuleGen_Greedy-RuleGen_Egglog))
$(eval $(call make-stats,random-3vars-100iters,RuleGen_Egglog-Ruler_Egglog))
$(eval $(call make-stats,random-3vars-100iters,RuleGen_Greedy-Ruler_Greedy))
$(eval $(call make-stats,random-3vars-100iters,RuleGen_Greedy-Ruler_Egglog))

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