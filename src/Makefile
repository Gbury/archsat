# copyright (c) 2014, guillaume bury

LOG=build.log
COMP=ocamlbuild -log $(LOG) # -classic-display
FLAGS=-use-ocamlfind

DOC=archsat.docdir/index.html
TEST=run_test.native
BIN=main.native

NAME=archsat
LIB=$(addprefix $(NAME), .cma .cmxa .cmxs)

all: bin test

top: lib
	utop

doc:
	$(COMP) $(FLAGS) $(DOC)

bin:
	$(COMP) $(FLAGS) $(BIN)

lib:
	$(COMP) $(FLAGS) $(LIB)

test:
	$(COMP) $(FLAGS) $(TEST)
	./$(TEST) -bt --colors --verbose | tee qcheck.log

test-long:
	$(COMP) $(FLAGS) $(TEST)
	./$(TEST) -bt --long --colors --verbose | tee qcheck.log

log:
	cat _build/$(LOG) || true

clean:
	$(COMP) -clean

.PHONY: clean doc all bin lib top test
