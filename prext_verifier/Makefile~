all:
	ocamlopt -w -A -o prextv -I z3-master/build/api/ml/ -cclib "-L. -lz3" nums.cmxa z3ml.cmxa Parser4prext.ml Smt4prext.ml  Prextv.ml

u1510:
	ocamlopt -w -A -o prextv -I 'ocamlfind query Z3' -cclib "-L. -lz3" nums.cmxa z3ml.cmxa Parser4prext.ml Smt4prext.ml  Prextv.ml

test:
	./prextv
