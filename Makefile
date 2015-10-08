
BIN=archsat
MAIN=src/main.native

all :
	cd src && $(MAKE)
	cp $(MAIN) $(BIN)

install: all
	./$(BIN) --help=groff > $(MANDIR)/man1/$(BIN).1
	cp $(BIN) $(BINDIR)/

uninstall:
	rm -f $(MANDIR)/man1/$(BIN).1 $(BINDIR)/$(BIN)

clean:
	cd src && $(MAKE) clean
	rm -f $(BIN)

