KNOWNTARGETS := CoqMakefile proof.zip
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

PROOF_ZIP_SOURCES := $(wildcard Profint.v Proof.v Makefile _CoqProject)

proof.zip: $(PROOF_ZIP_SOURCES)
	rm -f $@
	zip $@ -r $(PROOF_ZIP_SOURCES)

$(PROOF_ZIP_SOURCES):
	@true

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
