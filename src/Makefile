PROG        := parsleyc
MENHIR      := menhir
MENHIRFLAGS := --unused-tokens --explain --dump
OCAMLBUILD  := ocamlbuild -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS)" -cflag -annot

all:
	$(OCAMLBUILD) $(PROG).native
	-rm -f $(PROG) && ln -s $(PROG).native $(PROG)

clean:
	$(OCAMLBUILD) -clean
