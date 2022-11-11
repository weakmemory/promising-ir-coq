COQMODULE    := PromisingIR
COQTHEORIES  := \
	src/model/*.v \
	src/itree/*.v \
	src/prop/*.v \
	src/pf2ir/*.v \
	src/ldrfra/*.v \
	src/ldrfsc/*.v \
	src/sequential/*.v \
	src/optimizer/*.v \
	src/trans/*.v \

.PHONY: all theories clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src/model $(COQMODULE)"; \
	 echo "-R src/itree $(COQMODULE)"; \
	 echo "-R src/prop $(COQMODULE)"; \
	 echo "-R src/pf2ir $(COQMODULE)"; \
	 echo "-R src/ldrfra $(COQMODULE)"; \
	 echo "-R src/ldrfsc $(COQMODULE)"; \
	 echo "-R src/sequential $(COQMODULE)"; \
	 echo "-R src/optimizer $(COQMODULE)"; \
	 echo "-R src/trans $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
