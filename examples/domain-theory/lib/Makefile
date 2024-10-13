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

poset:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	filename="poset.ftl.tex"
	STEX_WRITESMS=true pdflatex $${filename}
	bibtex $${filename}
	STEX_USESMS=true pdflatex $${filename}
	STEX_USESMS=true pdflatex $${filename}

lattice:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	filename="lattice.ftl.tex"
	STEX_WRITESMS=true pdflatex $${filename}
	bibtex $${filename}
	STEX_USESMS=true pdflatex $${filename}
	STEX_USESMS=true pdflatex $${filename}
