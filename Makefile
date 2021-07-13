targets = pds.vo
srcs = equiv.v stack.v pds.v
docdir = docs
vobjs = $(srcs:.v=.vo)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)
pds.vo: equiv.vo stack.vo

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc --gallina -d $(docdir) $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
