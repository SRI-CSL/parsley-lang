PROG        := parsleyc
MENHIR      := menhir
MENHIRFLAGS := --unused-tokens --explain --dump
OCAMLBUILD  := ocamlbuild -package fmt -use-ocamlfind -use-menhir -menhir "$(MENHIR) $(MENHIRFLAGS)" -cflag -annot -cflag -g

all:
	$(OCAMLBUILD) $(PROG).native
	-rm -f $(PROG) && ln -s $(PROG).native $(PROG)

clean:
	$(OCAMLBUILD) -clean
