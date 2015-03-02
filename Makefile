
BIN=tabsat
MAIN=src/main.native

all:
	cd src && $(MAKE)
	cp $(MAIN) $(BIN)

clean:
	cd src && $(MAKE) clean
	rm -f $(BIN)
