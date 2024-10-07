.PHONY: example/Main clean
example/Main:
	cd example; agda --compile Main.agda
clean:
	rm -rf example/MAlonzo _build
