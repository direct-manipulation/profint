ROOT := $(shell git rev-parse --show-toplevel)

.PHONY: all clean sync

all:
	dune build \
	  --root=$(ROOT) \
	  --profile release \
	  src/ora.bc.js
	$(RM) ora.bc.js
	cp $(ROOT)/_build/default/src/ora.bc.js .

sync: all
	rsync -avz $(wildcard *.html ora.bc.js) \
	  chaudhuri.info:chaudhuri/research/profint

clean:
	dune clean --root=$(ROOT)
