eval $(opam config env)
make && OCAMLRUNPARAM=b ./parsleyc.exe fuzz test.ply --start NITFpacket

