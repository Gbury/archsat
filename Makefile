
BIN=archsat
MAIN=src/main.native

doc:
	cd doc && $(MAKE)

bin:
	cd src && $(MAKE) bin
	cp $(MAIN) $(BIN)

install: bin
	./$(BIN) --help=groff > $(MANDIR)/man1/$(BIN).1
	cp $(BIN) $(BINDIR)/

uninstall:
	rm -f $(MANDIR)/man1/$(BIN).1 $(BINDIR)/$(BIN)

clean:
	cd src && $(MAKE) clean
	rm -f $(BIN)

.PHONY: doc bin install uninstall clean

