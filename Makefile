VFILES=CastMonad.v DIPop.v DIStack.v Decidable.v \
	 DepEquiv.v Equiv.v HODepEquiv.v HoTT.v PreOrder.v\
	 Showable.v Vector.v

all: coqcompile doc

coqcompile:
	coq_makefile -R . "" *.v -o Makefile_coq
	$(MAKE) -f Makefile_coq > /dev/null

clean: 
	$(MAKE) -f Makefile_coq clean

doc: $(VFILES)
	mkdir -p html; \
	make coqcompile; \
	coqdoc --gallina -toc -interpolate -utf8 -html -R "." "" -d html $(VFILES)

html:
	$(MAKE) -f Makefile_coq html

%.native: %.ml
	ocamlbuild $@ 

# test: test_cast_extr.native
# 	./test_cast_extr.native || true

