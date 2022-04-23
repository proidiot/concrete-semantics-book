ISABELLE ?= isabelle

# TODO: Generate ROOT files

ARTIFACTS := artifacts/ch2.pdf artifacts/ch3.pdf
CLEANFILES := artifacts ch*/output

.PHONY: all
all: $(ARTIFACTS)

artifacts/ch%.pdf: ch%/ROOT ch%/*.thy
	mkdir -p $(@D)
	$(ISABELLE) build -v -D $(<D)
	cp $(<D)/output/document.pdf $@

.PHONY: clean
clean:
	rm -rf $(CLEANFILES)
