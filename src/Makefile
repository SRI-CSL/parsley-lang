.PHONY: update merge

update:
	@ dune build --force parsing/parseErrorMessages.messages.updated

merge: update
	@ dune build --force parsing/parseErrorMessages.messages.merged
