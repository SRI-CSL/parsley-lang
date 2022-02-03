.PHONY: all

EXE=parsleyc.exe

all: Makefile
	dune build
	cp _build/default/src/$(EXE) $(EXE)

clean:
	rm -f $(EXE)
	dune clean
