.PHONY: all

EXE=parsleyc.exe
AFLEXE=parsleyc_afl.exe

all: Makefile
	dune build src/$(EXE)
	cp _build/default/src/$(EXE) $(EXE)

afl: Makefile
	dune build --profile afl
	cp _build/default/src/$(EXE) $(AFLEXE)

clean:
	rm -f $(EXE)
	dune clean
