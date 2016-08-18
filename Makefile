COQC=coqc
SRC=$(wildcard *v)

all: jscoq udoc basic-cheatsheet.pdf cheatsheet.pdf $(SRC:%.v=%.html)

jscoq:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 jscoq
	cd jscoq && git checkout c219bd7e4b207846a607ce5a19513412d826ce7a


udoc:
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && git checkout 11fa04a621e8f8bc156430da4f0d3c10d8585ab3
	cd udoc && make # requires ocaml 4.02

basic-cheatsheet.pdf:
	make -C ssr-basic && cp ssr-basic/cheatsheet.pdf $@
       
cheatsheet.pdf:
	make -C ssr-cheat-sheet && cp ssr-cheat-sheet/cheatsheet.pdf $@


%.html : %.v
	-$(COQC) $* # if not working, no links but html still ok
	./udoc/udoc.byte $< -o $@
