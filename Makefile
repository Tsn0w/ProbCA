COQC=coqc
COQFLAGS=-R src ProbCA

VFILES := $(shell find src -name "*.v")
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	find src -name "*.vo*" -delete
	find src -name "*.glob" -delete
	find src -name ".*.aux" -delete
