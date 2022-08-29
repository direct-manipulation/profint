SOURCES := $(wildcard Profint/*.lean *.lean lean-toolchain)

proof.zip: $(SOURCES)
	rm -f $@
	zip $@ -r $(SOURCES)
