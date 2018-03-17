
BIN=archsat

all: $(BIN)
	@cd parsing && $(MAKE) --no-print-directory
	@cd include && $(MAKE) --no-print-directory
	@cd typing && $(MAKE) --no-print-directory
	@cd clauses && $(MAKE) --no-print-directory
	@cd logic && $(MAKE) --no-print-directory
	@cd equality && $(MAKE) --no-print-directory
	@cd quant && $(MAKE) --no-print-directory
	@cd rewr && $(MAKE) --no-print-directory

clean:
	rm -rf $(BIN)
	cd parsing && $(MAKE) clean --no-print-directory
	cd include && $(MAKE) clean --no-print-directory
	cd typing && $(MAKE) clean --no-print-directory
	cd clauses && $(MAKE) clean --no-print-directory
	cd logic && $(MAKE) clean --no-print-directory
	cd equality && $(MAKE) clean --no-print-directory
	cd quant && $(MAKE) clean --no-print-directory
	cd rewr && $(MAKE) clean --no-print-directory

$(BIN):
	@ln -f -s ../archsat $(BIN)

