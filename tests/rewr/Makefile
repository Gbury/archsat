
BIN=../archsat
OPT=-x +rwrt,+meta
DIR=rewr
TESTS= $(patsubst %,%.res,$(shell find . -name '*.smt2' -o -name '*.p' -o -name '*.zf' | sort -n))

all: $(TESTS)
	@echo -e "\e[32m[OK]\e[0m [$(DIR)]"

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< | grep Unsat > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			echo -e "cmd: $(BIN) $(OPT) $(DIR)/$<";			\
			exit 1;																			\
		fi

clean:


