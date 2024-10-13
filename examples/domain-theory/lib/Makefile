.ONESHELL:

all:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	for filename in *.ftl.tex; do
		STEX_WRITESMS=true pdflatex $${filename}
		bibtex $${filename}
		STEX_USESMS=true pdflatex $${filename}
		STEX_USESMS=true pdflatex $${filename}
	done
