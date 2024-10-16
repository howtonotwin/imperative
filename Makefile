.PHONY: all example/Main Pure clean

all: example/Main Pure ;
Pure:
	cd src; agda Imperative/Pure.agda
example/Main:
	cd example; agda --compile Main.agda
clean:
	rm -rf example/MAlonzo _build
