LATEXMK ?= latexmk
LATEXMK_FLAGS ?= -pdf -interaction=nonstopmode -halt-on-error
TARGET := RH_Q3

.PHONY: pdf bib clean distclean bundle qa

pdf:
	@echo "[Q3] Building $(TARGET).pdf..."
	@$(LATEXMK) $(LATEXMK_FLAGS) $(TARGET).tex

bib:
	@echo "[Q3] Building $(TARGET).pdf with bibliography..."
	@$(LATEXMK) $(LATEXMK_FLAGS) -bibtex $(TARGET).tex

clean:
	@echo "[Q3] Cleaning auxiliary files..."
	@$(LATEXMK) -c $(TARGET).tex

distclean: clean
	@rm -f $(TARGET).pdf

bundle: pdf
	@echo "[Q3] Bundle ready: $(TARGET).pdf"

qa:
	@echo "[Q3] QA sweep (clean + pdf + bibtex + log scan)..."
	@$(MAKE) -s clean
	@$(LATEXMK) $(LATEXMK_FLAGS) -bibtex $(TARGET).tex
	@! grep -E "Undefined reference|Label\\(s\\) may have changed" $(TARGET).log || (echo "[Q3] undefined references detected" && exit 1)
