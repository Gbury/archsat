# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) -use-ocamlfind -classic-display
FLAGS=
DIRS=-Is util,base
DOC=
TEST=tabsat.native

all: test

doc:
	$(COMP) $(FLAGS) $(DIRS) $(DOC)

build-test:
	$(COMP) $(FLAGS) $(DIRS) $(TEST)

test: build-test
	@echo "Done."

log:
	cat _build/$(LOG) || true

clean:
	$(COMP) -clean

.PHONY: clean doc all bench install uninstall reinstall
