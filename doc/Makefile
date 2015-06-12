
TARGET=concept
TEX=$(addprefix $(TARGET), .tex)
PDF=$(addprefix $(TARGET), .pdf)

all:
	rubber --pdf $(TEX)
	rubber --clean $(TEX)

clean:
	rubber --clean $(TEX)
	rm -f $(PDF)
