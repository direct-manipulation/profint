SOURCES := $(wildcard Profint/*.lean *.lean lean-toolchain)

proof.zip: $(SOURCES)
	rm -f $@
	lake clean
	zip $@ -r $(SOURCES)
