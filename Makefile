SITE = _site

all:
	$(MAKE) -C agda $@

html:
	@rm -rf $(SITE)
	@mkdir $(SITE)
	@echo "Generating html..."
	@cd agda; agda --html --html-dir=../$(SITE) Everything.agda
	@cd $(SITE); ln -s Everything.html index.html
