SHELL=/usr/bin/env bash

all:

ROOT := $(abspath $(CURDIR)/../..)

comp :=
define compare # (domain, bw, vars, iters)
$(eval comparefile := $(1)$(2)-$(3)vars-$(4)iters.json)
$(eval rulegen := results/rule_gen/$(1)$(2)-$(3)vars-$(4)iters-norm.json)
$(eval ruler := results/ruler/$(1)$(2)-$(3)vars-$(4)iters.json)
$(eval comp += $(ROOT)/$(comparefile))

$(ROOT)/$(rulegen):
	mkdir -p $(ROOT)/results/rule_gen
	@echo "Running $(1)$(2)-$(3)vars-$(4)iters-norm"
ifeq ($(1),bool)
	cd $(ROOT) && python3 rule_gen.py --mode $(1) --vars $(3) --max_length $(4) --opt_level irr-enum --norm
else
	cd $(ROOT) && python3 rule_gen.py --mode $(1) --bitwidth $(2) --vars $(3) --max_length $(4) --opt_level irr-enum --norm
endif

$(ROOT)/$(comparefile): $(ROOT)/$(rulegen)
	@echo "Comparing derivability for $(1)$(2)-$(3)vars-$(4)iters"
	cd $(ROOT) && python3 d.py --domain $(1)$(2) --vars $(3) --iters $(4)
endef

$(eval $(call compare,bool,,3,2))
$(eval $(call compare,bool,,3,3))
$(eval $(call compare,bv,4,3,2))
$(eval $(call compare,bv,4,3,3))
$(eval $(call compare,bv,32,3,2))
$(eval $(call compare,bv,32,3,3))
PRECIOUS: $(comp)

.PHONY: comp
comp: $(comp)

.PHONY: clean
clean:
	rm -f $(comp)

all: comp