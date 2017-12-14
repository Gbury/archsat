
BIN=archsat

all: $(BIN)
	@cd parsing && $(MAKE) --no-print-directory
	@cd include && $(MAKE) --no-print-directory
	@cd typing && $(MAKE) --no-print-directory
	@cd clauses && $(MAKE) --no-print-directory
	@cd logic && $(MAKE) --no-print-directory
	@cd equality && $(MAKE) --no-print-directory
	@cd quant && $(MAKE) --no-print-directory

clean:
	rm -rf $(BIN)
	cd parsing && $(MAKE) clean
	cd include && $(MAKE) clean
	cd typing && $(MAKE) clean

$(BIN):
	@ln -f -s ../archsat $(BIN)

