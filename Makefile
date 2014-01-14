#*****************************************************************#
#                                                                 #
#                        Dependent ML                             #
#                                                                 #
#                       (c) Hongwei Xi                            #
#                           July 2000                             #
#                                                                 #
#                   University of Cincinnati                      #
#                                                                 #
#                Distributed by permission only.                  #
#                                                                 #
#*****************************************************************#

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex

INCLUDES=
OCAMLFLAGS=$(INCLUDES)
OCAMLOPTFLAGS=$(INCLUDES)

dmltop.cmo: dmlparser.cmo

dmlparser.ml dmlparser.mli: dmlsyn.ml dmlparser.mly
	$(OCAMLYACC) -v dmlparser.mly

dmllexer.ml: dmllexer.mll dmlpar.ml
	$(OCAMLLEX) dmllexer.mll


#common rules:
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend
