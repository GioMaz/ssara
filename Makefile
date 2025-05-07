all: base extract

base:
	+make -C base
.PHONY: base

extract:
	+make -C extract
.PHONY: base

clean:
	+make -C base clean
	+make -C extract clean
.PHONY: clean
