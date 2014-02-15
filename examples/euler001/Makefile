
OBJS=euler001__Euler001.cmx main.cmx

NAME=main

OCAMLOPT=ocamlopt -noassert -inline 100

$(NAME).opt: $(OBJS)
	$(OCAMLOPT) -I /usr/local/lib/why3/ocaml \
	nums.cmxa why3__BuiltIn.cmx int__Int.cmx int__ComputerDivision.cmx \
	-o $@ $^

main.cmx: euler001__Euler001.cmx

euler001__Euler001.ml: ../euler001.mlw
	why3 -E ocaml ../euler001.mlw -o .

%.cmx: %.ml 
	ocamlopt -I /usr/local/lib/why3/ocaml -annot -c $<

%.cmo: %.ml 
	ocamlc -I /usr/local/lib/why3/ocaml -annot -c $<

%.cmi: %.mli 
	ocamlc -I /usr/local/lib/why3/ocaml -annot -c $<

clean::
	rm -f *.cm[xio] $(NAME).opt

