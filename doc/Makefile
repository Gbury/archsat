
TARGET=concept
TEX=$(addprefix $(TARGET), .tex)
PDF=$(addprefix $(TARGET), .pdf)

all:
	rubber --pdf $(TEX)
	rubber --clean $(TEX)

clean:
	rm -f $(PDF)
