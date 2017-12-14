
BIN=../archsat
OPT=--no-type --no-solve
DIR=parsing
TESTS=$(patsubst %,%.res,$(shell find . -name '*.p' | sort -n))

all: $(TESTS)
	@echo -e "\e[32m[OK]\e[0m [$(DIR)]"

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			exit 1;																			\
		fi

clean:


