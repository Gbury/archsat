# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) -classic-display
FLAGS=-use-ocamlfind -use-menhir -yaccflag '--explain'
DIRS=-Is util,base,core,input
DOC=tabsat.docdir/index.html
TEST=main.native

NAME=tabsat
LIB=$(addprefix $(NAME), .cma .cmxa .cmxs)

all: build-lib test

doc:
	$(COMP) $(FLAGS) $(DIRS) $(DOC)

build-test:
	$(COMP) $(FLAGS) $(DIRS) $(TEST)

test: build-test

build-lib:
	$(COMP) $(FLAGS) $(DIRS) $(LIB)

lib: build-lib
	@echo "Lib compiled."

log:
	cat _build/$(LOG) || true

clean:
	$(COMP) -clean

.PHONY: clean doc all bench install uninstall reinstall
