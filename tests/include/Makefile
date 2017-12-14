
BIN=../archsat
OPT=
DIR=include
TESTS=$(patsubst %,%.res,$(shell find . -name '*.p' | sort -n))

all: $(TESTS)

%.res: % $(BIN)
	@if ! $(BIN) $(OPT) $< > /dev/null; then 							\
			echo -e "\e[31m[KO]\e[0m [$(DIR)] $<";			\
			exit 1;																			\
		else																					\
			echo -e "\e[32m[OK]\e[0m [$(DIR)] $<";			\
		fi

clean:


