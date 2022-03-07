# Static/shared file handling

# =============
# General rules
# =============

all: dk

uninstall:
	rm -rf $(SHAREDIR)/*

clean:
	rm -rf .depend *.dko


# ========
# DK files
# ========

DK_FILES=logic.dko classical.dko epsilon.dko
DKC  := $(shell command -v dkcheck 2> /dev/null)
DKD  := $(shell command -v dkdep 2> /dev/null)

dk: $(DK_FILES)

install_dk: dk
	mkdir -p $(SHAREDIR)/dk
	cp *.dk *.dko $(SHAREDIR)/dk/

# =====================
# Dependency generation
# =====================

include .depend

.depend:
ifdef DKD
	dkdep -o .depend *.dk
else
	echo "Skipping dependency analysis"
endif


# ===============================
# Rules to compile DK axiom files
# ===============================

%.dko: %.dk
ifdef DKC
	dkcheck -e $<
else
	echo "Skipping compilation of $<"
endif

