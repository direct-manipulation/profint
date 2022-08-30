SOURCES := $(wildcard Profint/*.lean *.lean lean-toolchain)

proof.zip: $(SOURCES)
	rm -f $@
	zip $@ -r $(SOURCES)

.PHONY: all
all: $(SOURCES)
	lake build
