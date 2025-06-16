COQC=coqc
COQFLAGS=-R src ProbCA

VFILES := \
  src/Common.v \
  src/Expressions.v \
  src/Probability.v \
  src/ProbCA.v \
  src/ModelHOL.v

VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	find src -name "*.vo*" -delete
	find src -name "*.glob" -delete
	find src -name ".*.aux" -delete
