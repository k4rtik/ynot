all:
	$(MAKE) -C src/coq
#	$(MAKE) -C examples

cleandep:
	rm */.depend

clean:
	$(MAKE) -C src/coq clean
#	$(MAKE) -C examples clean
#	$(MAKE) -C doc clean

doc:
	$(MAKE) -C doc

coqtop:
	coqtop -R src Ynot -R examples Examples

.PHONY: all clean coqtop cleandep dist doc install
