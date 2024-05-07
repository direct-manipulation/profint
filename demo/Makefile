PROFJS := src/profint/profint_jsoo.bc.js
ROOT := $(shell git rev-parse --show-toplevel)
PROFILE := release
# PROFILE := dev
DELIVERABLES := $(wildcard *.html favicon.ico icons $(notdir $(PROFJS)) demo.js vendor)

.PHONY: all clean sync list serve

all:
	dune build \
	  --root=$(ROOT) \
	  --profile $(PROFILE) \
	  $(PROFJS)
	$(RM) $(notdir $(PROFJS))
	cp $(ROOT)/_build/default/$(PROFJS) .
	mkdir -p vendor
	mkdir -p vendor/iconfont
	cp -a $(ROOT)/node_modules/material-icons/iconfont/filled.css vendor/iconfont/
	cp -a $(ROOT)/node_modules/material-icons/iconfont/material-icons.woff2 vendor/iconfont/
	cp -a $(ROOT)/node_modules/material-icons/iconfont/material-icons.woff vendor/iconfont/
	cp -a $(ROOT)/node_modules/jquery/dist/jquery.min.js vendor/
	cp -a $(ROOT)/node_modules/jquery-color/dist/jquery.color.min.js vendor/
	cp -a $(ROOT)/node_modules/ace-builds/src-min/ace.js vendor/
	cp -a $(ROOT)/node_modules/ace-builds/src-min/theme-chrome.js vendor/
	cp -a $(ROOT)/node_modules/katex/dist/katex.min.css vendor/
	cp -a $(ROOT)/node_modules/katex/dist/katex.min.js vendor/
	cp -a $(ROOT)/node_modules/katex/dist/fonts vendor/
	cp -a $(ROOT)/node_modules/hotkeys-js/dist/hotkeys.min.js vendor/
	cp -a $(ROOT)/node_modules/jszip/dist/jszip.min.js vendor/
	cp -a $(ROOT)/node_modules/file-saver/dist/FileSaver.min.js vendor/

sync: all
	rsync -avz $(DELIVERABLES) chaudhuri.info:chaudhuri/research/profint

clean:
	dune clean --root=$(ROOT)

list:
	@echo ROOT $(ROOT)
	@echo DELIVERABLES $(DELIVERABLES)

serve: all
	python3 -m http.server 8080
