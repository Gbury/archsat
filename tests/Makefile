
BIN=archsat

all: check solve prove

check: $(BIN)
	@cd parsing && $(MAKE) --no-print-directory
	@cd include && $(MAKE) --no-print-directory
	@cd typing && $(MAKE) --no-print-directory

solve: $(BIN)
	@cd clauses && $(MAKE) -f Makefile.solve --no-print-directory
	@cd logic && $(MAKE) -f Makefile.solve --no-print-directory
	@cd equality && $(MAKE) -f Makefile.solve --no-print-directory
	@cd quant && $(MAKE) -f Makefile.solve --no-print-directory
	@cd poly && $(MAKE) -f Makefile.solve --no-print-directory
	@cd rewr && $(MAKE) -f Makefile.solve --no-print-directory
	@cd bugs && $(MAKE) -f Makefile.solve --no-print-directory

prove: solve $(BIN)
	@cd clauses && $(MAKE) -f Makefile.prove --no-print-directory
	@cd logic && $(MAKE) -f Makefile.prove --no-print-directory
	@cd equality && $(MAKE) -f Makefile.prove --no-print-directory
	@cd quant && $(MAKE) -f Makefile.prove --no-print-directory
	@cd poly && $(MAKE) -f Makefile.prove --no-print-directory
	@cd rewr && $(MAKE) -f Makefile.prove --no-print-directory
	@cd bugs && $(MAKE) -f Makefile.prove --no-print-directory

clean:
	@rm -rf $(BIN)
	@cd parsing 	&& $(MAKE) clean --no-print-directory
	@cd include 	&& $(MAKE) clean --no-print-directory
	@cd typing 		&& $(MAKE) clean --no-print-directory
	@cd clauses 	&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd logic 		&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd equality 	&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd quant 		&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd poly 			&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd rewr 			&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd bugs 			&& $(MAKE) clean -f Makefile.solve --no-print-directory
	@cd clauses 	&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd logic 		&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd equality 	&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd quant 		&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd poly 			&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd rewr 			&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@cd bugs 			&& $(MAKE) clean -f Makefile.prove --no-print-directory
	@echo "Cleaned tests artifact files"

$(BIN):
	@ln -f -s ../archsat $(BIN)

