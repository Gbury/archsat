
BIN=../archsat
OPT=
DIR=clauses
TESTS= $(patsubst %,%.res,$(shell find . -name '*.cnf' | sort -n))

all: $(TESTS)

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			exit 1;																			\
		else																					\
			echo -e "\e[32m[OK]\e[0m [$(DIR)] $<";			\
		fi

clean:


