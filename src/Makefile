# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) # -classic-display
FLAGS=-use-ocamlfind -use-menhir -yaccflag '--explain'
DIRS=-Is util,base,core,input,parsers,algos
DOC=tabsat.docdir/index.html
BIN=main.native

NAME=tabsat
LIB=$(addprefix $(NAME), .cma .cmxa .cmxs)

all: bin

doc:
	$(COMP) $(FLAGS) $(DIRS) $(DOC)

build-bin:
	$(COMP) $(FLAGS) $(DIRS) $(BIN)

bin: build-bin

build-lib:
	$(COMP) $(FLAGS) $(DIRS) $(LIB)

lib: build-lib
	@echo "Lib compiled."

log:
	cat _build/$(LOG) || true

clean:
	$(COMP) -clean

.PHONY: clean doc all bin lib build-bin build-lib
