SHELL=/usr/bin/env bash

all:

ROOT := $(abspath $(CURDIR)/../..)

rules :=

define run-rulegen # (mode, bw, vars, iters, opt_level)
$(eval file := $(if $(filter bv, $(1)), \
	results/rule_gen/$(1)$(2)-$(3)vars-$(4)iters-$(5).json, \
	results/rule_gen/bool-$(3)vars-$(4)iters-$(5).json))
$(eval rules += $(ROOT)/$(file))
$(ROOT)/$(file): $(ROOT)/rule_gen.py
	mkdir -p $(ROOT)/results/rule_gen
	@echo "Running $(1)$(2)-$(3)vars-$(4)iters-$(5)"
	cd $(ROOT) && python3 rule_gen.py --mode $(1) --bitwidth $(2) --vars $(3) --max_length $(4) --opt_level $(5) --no-norm
endef

PRECIOUS: $(rules)

$(eval $(call run-rulegen,bool,4,3,2,direct))
$(eval $(call run-rulegen,bool,4,3,2,rule-app))
$(eval $(call run-rulegen,bool,4,3,2,irr-enum))

$(eval $(call run-rulegen,bv,4,3,2,direct))
$(eval $(call run-rulegen,bv,4,3,2,rule-app))
$(eval $(call run-rulegen,bv,4,3,2,irr-enum))

#$(eval $(call run-rulegen,bv,4,3,3,direct))
#$(eval $(call run-rulegen,bv,4,3,3,rule-app))
#$(eval $(call run-rulegen,bv,4,3,3,irr-enum))

.PHONY: latex-table
latex-table: $(rules)
	python3 make_table.py $^ | pandoc -f csv -t latex --columns 200 \
	| sed 's|{@{}llllllllll@{}}|{@{}lrrlrrrrrr@{}}|' \
	| sed 's/tabularnewline/\\/' \
	| awk 'BEGIN { count=-1 } /\\\\$$/ {print; count++; if (count % 3 == 0 && count > 0 && count < 6) print "\\midrule"; next } { print }'

.PHONY: table
table: $(rules)
	python3 make_table.py $^ | xsv table

.PHONY: clean
clean:
	rm -f $(rules)

all: table