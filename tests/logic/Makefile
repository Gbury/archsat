
BIN=../archsat
OPT=--infer
DIR=logic
TESTS= $(patsubst %,%.res,$(shell find . -name '*.smt2' -o -name '*.p' | sort -n))

all: $(TESTS)
	@echo -e "\e[32m[OK]\e[0m [$(DIR)]"

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< | grep Unsat > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			exit 1;																			\
		fi

clean:


