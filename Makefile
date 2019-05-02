default: website

AGDA_FILES=`find . -name '*.lagda'`

website:
	cd tspl
	for file in $(AGDA_FILES); do agda --html $$file; done

install:
	mkdir -p $(out)
	cp *.html $(out)

clean:
	rm -rf html
