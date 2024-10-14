.ONESHELL:

all:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	for filename in *.ftl.tex; do
		filename=$$(echo "$${filename%.ftl.tex}")
		STEX_WRITESMS=true pdflatex $${filename}.ftl.tex
		bibtex $${filename}.ftl
		STEX_USESMS=true pdflatex $${filename}.ftl.tex
		STEX_USESMS=true pdflatex $${filename}.ftl.tex
		rm $${filename}.ftl.aux
		rm $${filename}.ftl.bbl
		rm $${filename}.ftl.blg
		rm $${filename}.ftl.log
		rm $${filename}.ftl.out
		rm $${filename}.ftl.sms
		rm $${filename}.ftl.sref
		rm $${filename}.ftl.upa
		rm $${filename}.ftl.upb
	done

poset:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	filename="poset"
	STEX_WRITESMS=true pdflatex $${filename}.ftl.tex
	bibtex $${filename}.ftl
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	rm $${filename}.ftl.aux
	rm $${filename}.ftl.bbl
	rm $${filename}.ftl.blg
	rm $${filename}.ftl.log
	rm $${filename}.ftl.out
	rm $${filename}.ftl.sms
	rm $${filename}.ftl.sref
	rm $${filename}.ftl.upa
	rm $${filename}.ftl.upb

complete-lattice:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	filename="complete-lattice"
	STEX_WRITESMS=true pdflatex $${filename}.ftl.tex
	bibtex $${filename}.ftl
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	rm $${filename}.ftl.aux
	rm $${filename}.ftl.bbl
	rm $${filename}.ftl.blg
	rm $${filename}.ftl.log
	rm $${filename}.ftl.out
	rm $${filename}.ftl.sms
	rm $${filename}.ftl.sref
	rm $${filename}.ftl.upa
	rm $${filename}.ftl.upb

lattice:
	export MATHHUB=$$(realpath ../..) # set MATHHUB to naproche/examples
	cd ../source
	filename="lattice"
	STEX_WRITESMS=true pdflatex $${filename}.ftl.tex
	bibtex $${filename}.ftl
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	STEX_USESMS=true pdflatex $${filename}.ftl.tex
	rm $${filename}.ftl.aux
	rm $${filename}.ftl.bbl
	rm $${filename}.ftl.blg
	rm $${filename}.ftl.log
	rm $${filename}.ftl.out
	rm $${filename}.ftl.sms
	rm $${filename}.ftl.sref
	rm $${filename}.ftl.upa
	rm $${filename}.ftl.upb
