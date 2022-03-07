
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

static:
	cd static && $(MAKE)

test: test-lib test-bin

test-lib:
	@echo "RUN API tests"
	$(MAKE) -C src test

test-bin: bin static
	@echo "run BIN tests…"
	@cd tests && $(MAKE) --no-print-directory
	$(MAKE) test-clean

test-clean:
	@cd tests && $(MAKE) --no-print-directory clean

install: bin
	./$(BIN) --help=groff > $(MANDIR)/man1/$(BIN).1
	cp $(BIN) $(BINDIR)/

uninstall:
	rm -f $(MANDIR)/man1/$(BIN).1 $(BINDIR)/$(BIN)

clean:
	cd src && $(MAKE) clean
	cd tests && $(MAKE) clean
	cd static && $(MAKE) clean
	rm -f $(BIN) perf.* *.v* *tmp* *.gv *.glob *.dk

.PHONY: doc bin lib static test test-lib test-bin install uninstall clean

