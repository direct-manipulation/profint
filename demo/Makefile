ROOT := $(shell git rev-parse --show-toplevel)
PROFILE := release
# PROFILE := dev
DELIVERABLES := $(wildcard *.html favicon.ico icons ora.bc.js lean4)

.PHONY: all clean sync list

all:
	dune build \
	  --root=$(ROOT) \
	  --profile $(PROFILE) \
	  src/ora.bc.js
	$(RM) ora.bc.js
	cd lean4 && $(MAKE)
	cp $(ROOT)/_build/default/src/ora.bc.js .

sync: all
	rsync -avz $(DELIVERABLES) chaudhuri.info:chaudhuri/research/profint

clean:
	dune clean --root=$(ROOT)

list:
	@echo ROOT $(ROOT)
	@echo DELIVERABLES $(DELIVERABLES)
