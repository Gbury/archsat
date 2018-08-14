
FILES=logic.dko classical.dko epsilon.dko

all: $(FILES)

%.dko: %.dk
	dkcheck -e $<

.depend:
	dkdep -o .depend *.dk

clean:
	rm .depend *.dko

include .depend
