### Compilers and flags ###

HC = ghc
HFLAGS = -O2 -XPolymorphicComponents -XFlexibleInstances -XFlexibleContexts

STRIP = strip

### Targets ###

ALICE = alice

ALICEDIR = Alice
BUILDDIR = .build

BUILDOPT = -odir $(BUILDDIR) -hidir $(BUILDDIR)
PROFLOPT = -prof -auto-all -osuf p.o -hisuf p.hi $(BUILDOPT)
COVEROPT = -fhpc -osuf hpc.o -hisuf hpc.hi $(BUILDOPT)

all: $(ALICE)
prof: $(ALICE).p
hpc: $(ALICE).hpc

.PHONY: all prof hpc $(ALICE) $(ALICE).p $(ALICE).hpc \
	source binary getall clean depend

### Alice ###

$(ALICE):	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(BUILDOPT)
	$(if $(STRIP),$(STRIP) -s $@)

$(ALICE).p:	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(PROFLOPT)
	$(if $(STRIP),$(STRIP) -s $@)

$(ALICE).hpc:	$(BUILDDIR)
	$(HC) --make $(ALICEDIR)/Main.hs -o $@ $(HFLAGS) $(COVEROPT)
	$(if $(STRIP),$(STRIP) -s $@)


 ### Create build directories ###
 
$(BUILDDIR):
	mkdir -p $@


### Janitory ###

clean:
	rm -rf $(ALICE) $(ALICE).p $(ALICE).hpc .hpc $(BUILDDIR) core

depend:
	makedepend -Y -p $(BUILDDIR)/
	rm Makefile.bak

### Release ###

TAR = tar --transform='s=^=$(RELNAME)/='

RELNAME = sad-$(shell git-describe | cut -d- -f-2)
RELBIN  = $(RELNAME).i386

COMMON = $(SUBDIR) $(TOPDIR)
SUBDIR = Alice moses doc examples
TOPDIR = Makefile COPYING README init.opt
SOURCE = $(COMMON) provers/provers.dat
BINARY = $(SOURCE) alice provers/moses
GETALL = $(COMMON) alice provers

source:
	$(TAR) -czf $(RELNAME).tar.gz $(SOURCE)

binary: all
	$(TAR) -cjf $(RELBIN).tar.bz2 $(BINARY)

getall: all
	$(TAR) -cjf $(RELBIN).tar.bz2 $(GETALL)
