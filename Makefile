all :
	ocamlbuild -yaccflag -v -lib unix Basic/main.native; ln -fs main.native resol
	ocamlbuild -yaccflag -v -lib unix Watched_literals/main-wl.native; ln -fs main-wl.native resol-wl

byte :
	ocamlbuild -yaccflag -v -lib unix Basic/main.byte; ln -fs main.byte resol
	ocamlbuild -yaccflag -v -lib unix Watched_literals/main-wl.byte; ln -fs main-wl.byte resol-wl
clean:
	ocamlbuild -clean
