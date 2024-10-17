.ONESHELL:

# Setup for the build function (see below): Set MATHHUB to "naproche/examples"
# and enter the source directory of this archive.
define setup
	export MATHHUB=$$(realpath ../..)
	cd ../source
endef

# Given <name> as argument, compile the file <name>.ftl.tex (in the current
# directory) to PDF:
# Run pdflatex over <name>.ftl.tex; if that succeeds, do the following:
# Run bibtex over <name>.ftl, then again two times pdflatex over <name>.ftl.tex,
# then delete all files of the form <name>.ftl.* except <name>.ftl.tex and
# <name>.ftl.pdf.
define build
	filename="$(1)"
	STEX_WRITESMS=true pdflatex $${filename}.ftl.tex && \
	{ \
		bibtex $${filename}.ftl
		STEX_USESMS=true pdflatex $${filename}.ftl.tex ; \
		STEX_USESMS=true pdflatex $${filename}.ftl.tex ; \
		for artefact in $${filename}.ftl.*; do
			if [[ ( $${artefact} != *.tex ) && ( $${artefact} != *.pdf ) ]]; then
				rm "$${artefact}"
			fi
		done \
	}
endef

# Compile all .ftl.tex files in the source directory to PDF.
all:
	@$(call setup)
	for filename in *.ftl.tex; do
		filename=$$(echo "$${filename%.ftl.tex}")
		@$(call build,"$${filename}")
	done

# Compile source/poset.ftl.tex to PDF.
poset:
	@$(call setup)
	@$(call build,"poset")

# Compile source/complete-lattice.ftl.tex to PDF.
complete-lattice:
	@$(call setup)
	@$(call build,"complete-lattice")

# Compile source/lattice.ftl.tex to PDF.
lattice:
	@$(call setup)
	@$(call build,"lattice")
