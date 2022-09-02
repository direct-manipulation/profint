ROOT := $(shell git rev-parse --show-toplevel)
PROFILE := release
# PROFILE := dev
PSYS := lean4 lean3 coq coq_reflect
DELIVERABLES := $(wildcard *.html favicon.ico icons ora.bc.js $(PSYS))

.PHONY: all clean sync list

all:
	dune build \
	  --root=$(ROOT) \
	  --profile $(PROFILE) \
	  src/ora.bc.js
	$(RM) ora.bc.js
	for d in $(PSYS) ; do ( cd $$d ; $(MAKE) proof.zip ) ; done
	cp $(ROOT)/_build/default/src/ora.bc.js .

sync: all
	for d in $(PSYS) ; do ( cd $$d ; git clean -fxd . ; $(MAKE) proof.zip ) ; done
	rsync -avz $(DELIVERABLES) chaudhuri.info:chaudhuri/research/profint

clean:
	dune clean --root=$(ROOT)

list:
	@echo ROOT $(ROOT)
	@echo DELIVERABLES $(DELIVERABLES)
