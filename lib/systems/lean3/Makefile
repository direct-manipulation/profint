SOURCES := $(wildcard src/Profint.lean src/Proof.lean lean-toolchain leanpkg.toml)

proof.zip: $(SOURCES)
	rm -f $@
	zip $@ -r $(SOURCES)

.PHONY: all
all: $(SOURCES)
	leanpkg build
