
# DICoq
Dependent Interoperability for Coq

The repository contains the companion code of the publication
"Foundations of Dependent Interoperability" (submitted to JFP).

Note that there are two branches (one for the JFP submission, one
for the ICFP'16 publication)

To compile:

   make coqcompile

To run the example:

$ ocaml -init distack.ml

> (exec 0 0 (IPlus 0) [1;2] : int list);;

	int list = [3]

> exec 0 0 (IPlus 0) [];;

	Segmentation fault: 11 

> simple_exec NPlus [1;2];;

	int list = [3]

> simple_exec NPlus [];;

	Exception: (Failure "Cast failure: invalid instruction").   
