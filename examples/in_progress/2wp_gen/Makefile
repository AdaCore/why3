SHELL=/bin/bash
REPLAY=why3 replay -f -L .
MLW=base choice ho_set ho_rel fn pfn order transfinite game game_no_strat game_simulation subgame game_logic

replay:
	@exe() { echo "$$0 $$@"; "$$@"; };\
	for f in $(MLW); do exe $(REPLAY) $$f; done
