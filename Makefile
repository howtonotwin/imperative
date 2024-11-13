.PHONY: all example/Main Pure html clean

all: example/Main Pure ;
Pure:
	cd src; agda Imperative/Pure.agda
example/Main:
	cd example; agda --compile Main.agda
clean:
	rm -rf example/MAlonzo _build
html:
	cd src; find . -name '*.lagda.md' -exec agda --html --html-dir=../html --html-highlight=auto {} \;
	cd example; find . -name '*.lagda.md' -exec agda --html --html-dir=../html --html-highlight=auto {} \;
	mkdir -p html
	echo ".Agda, code { font-family: JuliaMono, monospace; }" >> html/Agda.css
	echo ".Agda :target { background-color: lightskyblue; }" >> html/Agda.css
	for md in html/*.md; do \
		name=$${md#html/}; name=$${name%.md}; \
		[ -e "$$md" ] && pandoc -s "$$md" -o "html/$$name.html" \
			--metadata title="$$name" --css Agda.css -V document-css -V maxwidth=80em; \
	done
