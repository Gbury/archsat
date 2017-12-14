
BIN=../archsat
OPT=
DIR=clauses
TESTS= $(patsubst %,%.res,$(shell find . -name '*.cnf' | sort -n))

all: $(TESTS)
	@echo -e "\e[32m[OK]\e[0m [$(DIR)]"

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< | grep Unsat > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			exit 1;																			\
		fi

clean:


