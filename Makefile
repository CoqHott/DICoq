all: coqcompile 

coqcompile: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

clean: 
	$(MAKE) -f Makefile.coq clean

doc: $(VFILES)
	mkdir -p html; \
	make coqcompile; \
	coqdoc --gallina -toc -interpolate -utf8 -html -R "." "" -d html $(VFILES)

html:
	$(MAKE) -f Makefile.coq html

%.native: %.ml
	ocamlbuild $@ 

# test: test_cast_extr.native
# 	./test_cast_extr.native || true

