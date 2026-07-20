SITE = _site

all:
	$(MAKE) -C categorical-combinators $@
	$(MAKE) -C combinatory-logic $@

html:
	@rm -rf $(SITE)
	@mkdir $(SITE)
	@echo "Generating html..."
	@cd categorical-combinators; agda --html --html-dir=../$(SITE) Everything.agda
	@cd $(SITE); ln -s Everything.html index.html
