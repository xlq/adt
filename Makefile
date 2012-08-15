.PHONY: all clean

all:
	ocamlbuild main.d.byte -cflags -w,-8 -libs nums
	# ocamlbuild main.d.byte -libs nums

clean:
	ocamlbuild -clean main.d.byte
