
BIN=archsat
MAIN=src/main.native

all: test-bin

doc:
	cd doc && $(MAKE)

bin:
	$(MAKE) -C src bin
	cp $(MAIN) $(BIN)

lib:
	$(MAKE) -C src lib

test: test-lib test-bin

test-lib: lib
	@echo "RUN API tests"
	$(MAKE) -C src test

test-bin: bin
	@echo "run BIN tests…"
	@cd tests && $(MAKE) --no-print-directory

install: bin
	./$(BIN) --help=groff > $(MANDIR)/man1/$(BIN).1
	cp $(BIN) $(BINDIR)/

uninstall:
	rm -f $(MANDIR)/man1/$(BIN).1 $(BINDIR)/$(BIN)

clean:
	cd src && $(MAKE) clean
	cd tests && $(MAKE) clean
	rm -f $(BIN) perf.* *.v* *tmp*

.PHONY: doc bin install uninstall clean

