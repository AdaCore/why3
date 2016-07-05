SHELL=/bin/bash
REPLAY=why3 replay -L . -f
MLW=base choice ho_set ho_rel fn order transfinite game game_fmla transition

replay:
	@exe() { echo "$$0 $$@"; "$$@"; };\
	for f in $(MLW); do exe $(REPLAY) $$f.mlw; done
