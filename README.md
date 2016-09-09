
# DICoq
Dependent Interoperability for Coq

The repository contains the companioon code of the publication
Partial Type Equivalences for Verified Dependent Interoperability (ICFP'16).


To compile:

   make coqcompile

To run the example:

$ ocaml -init distack.ml
# (exec 0 0 (IPlus 0) [1;2] : int list);;
- : int list = [3]
# exec 0 0 (IPlus 0) [];;
Segmentation fault: 11 

# simple_exec NPlus [1;2];;
- : int list = [3]                                                                              
# simple_exec NPlus [];;
Exception: (Failure "Cast failure: invalid instruction").   
