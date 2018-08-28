
FILES=logic.dko classical.dko epsilon.dko
DKC  := $(shell command -v dkcheck 2> /dev/null)
DKD  := $(shell command -v dkdep 2> /dev/null)

all: $(FILES)

%.dko: %.dk
ifdef DKC
	dkcheck -e $<
else
	echo "Skipping compilation of $<"
endif

.depend:
ifdef DKD
	dkdep -o .depend *.dk
else
	echo "Skipping dependency analysis"
endif

clean:
	rm .depend *.dko

include .depend
