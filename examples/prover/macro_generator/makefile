
ML=Priv Macrogen_decls Macrogen_printing Macrogen_params Macrogen_theory Macrogen_transform Macrogen_nlparams Macrogen_nameless
MLI=Macrogen_params_sig Macrogen_printing_sig Macrogen_nlparams_sig
DP=./depend/
BD=./build/
SRC=./
CMX=$(patsubst %,$(BD)%.cmx,$(ML))
CMI=$(patsubst %,$(BD)%.cmi,$(ML) $(MLI))
MLC=ocamlopt.opt
INCLUDES=-I $(BD)
MLFLAGS=
MLIFLAGS=
MLEXECFLAGS=

$(BD)macrogen: $(CMX) Macrogen.ml
	$(MLC) $(INCLUDES) $(MLFLAGS) $(MLEXECFLAGS) -o $(BD)macrogen $(CMX) $(SRC)Macrogen.ml

$(BD)%.cmi:$(DP)%.mli.depend
	$(MLC) $(INCLUDES) $(MLIFLAGS) -c -o $@ $(SRC)$*.mli

$(BD)%.cmx:$(DP)%.ml.depend $(BD)%.cmi
	$(MLC) $(INCLUDES) $(MLFLAGS) -c -o $@ $(SRC)$*.ml

$(DP)%.depend:$(SRC)%
	touch $@

$(DP)Priv.ml.depend:

$(DP)Priv.mli.depend:

$(DP)Macrogen_decls.mli.depend: $(BD)Priv.cmi

$(DP)Macrogen_decls.ml.depend: $(BD)Priv.cmi

$(DP)Macrogen_printing.mli.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params.cmi $(BD)Macrogen_printing_sig.cmi

$(DP)Macrogen_printing.ml.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params.cmi $(BD)Macrogen_printing_sig.cmi

$(DP)Macrogen_theory.ml.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_printing.cmi

$(DP)Macrogen_theory.mli.depend: $(BD)Macrogen_params.cmi $(BD)Macrogen_decls.cmi $(BD)Macrogen_printing.cmi

$(DP)Macrogen_nameless.ml.depend: $(BD)Macrogen_nlparams.cmi $(BD)Macrogen_decls.cmi $(BD)Macrogen_printing.cmi

$(DP)Macrogen_nameless.mli.depend: $(BD)Macrogen_nlparams.cmi $(BD)Macrogen_decls.cmi $(BD)Macrogen_printing.cmi

$(DP)Macrogen_params.mli.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params_sig.cmi

$(DP)Macrogen_params.ml.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params_sig.cmi

$(DP)Macrogen_nlparams.mli.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params.cmi $(BD)Macrogen_nlparams_sig.cmi

$(DP)Macrogen_nlparams.ml.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params.cmi $(BD)Macrogen_nlparams_sig.cmi

$(DP)Macrogen_transform.ml.depend: $(BD)Macrogen_decls.cmi

$(DP)Macrogen_transform.mli.depend: $(BD)Macrogen_decls.cmi

$(DP)Macrogen_printing_sig.mli.depend: $(BD)Macrogen_params.cmi

$(DP)Macrogen_params_sig.mli.depend: $(BD)Macrogen_decls.cmi

$(DP)Macrogen_nlparams_sig.mli.depend: $(BD)Macrogen_decls.cmi $(BD)Macrogen_params.cmi

.SECONDARY:

.PHONY: clean restore

clean:
	rm -f $(BD)*.o $(BD)*.cmi $(BD)*.cmx $(DP)*.depend

restore: clean
	rm -f $(BD)macrogen


