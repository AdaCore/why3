SHELL=/bin/bash
REPLAY=why3 replay -L .
MLW=base choice ho_set ho_rel fn order transfinite game game_fmla

replay:
	@exe() { echo "$$0 $$@"; "$$@"; };\
	for f in $(MLW); do exe $(REPLAY) $$f.mlw; done
