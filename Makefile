all: jscoq basic-cheatsheet.pdf cheatsheet.pdf

jscoq:
	git clone https://github.com/ejgallego/jscoq-builds.git --depth 1 jscoq
	cd jscoq && git checkout c219bd7e4b207846a607ce5a19513412d826ce7a

basic-cheatsheet.pdf:
	make -C ssr-basic && cp ssr-basic/cheatsheet.pdf $@
       
cheatsheet.pdf:
	make -C ssr-cheat-sheet && cp ssr-cheat-sheet/cheatsheet.pdf $@
