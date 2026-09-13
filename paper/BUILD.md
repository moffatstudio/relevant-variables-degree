# Building the paper

## Status on this machine (2026-09-13)

**No LaTeX compiler is installed.** Checked and not found:

- `pdflatex`, `latexmk`, `tectonic`, `xelatex` on `PATH` (`where.exe`)
- `C:/Users/moffa/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe`
- `C:/texlive/*/bin/win*/pdflatex.exe` (no `C:/texlive` directory at all)
- no TeX-looking folder under `C:/Program Files` or `C:/Users/moffa/AppData/Local/Programs`

So `main.pdf` has **not** been produced. The source was linted instead (see below).

## Compile command (once a TeX distribution is installed)

`main.tex` uses a hand-written `thebibliography`, so **no bibtex/biber run is needed**:

```sh
cd paper
pdflatex main.tex
pdflatex main.tex     # second pass resolves \ref, \eqref and the table number
```

or, equivalently,

```sh
latexmk -pdf main.tex
```

or, with a self-contained compiler that downloads its own packages:

```sh
tectonic main.tex
```

### Installing a compiler on this machine

MiKTeX is the lightest option on Windows and installs missing packages on demand:

```powershell
winget install MiKTeX.MiKTeX
# then, in a fresh shell:
pdflatex --version
```

Alternatively `winget install TeXLive.TeXLive` (much larger), or download a single
`tectonic.exe` from <https://tectonic-typesetting.github.io/> and put it on `PATH`.

### Packages required

All are in a standard TeX Live / MiKTeX installation:
`amsart` (document class), `amsmath`, `amssymb`, `amsthm`, `mathtools`, `geometry`,
`booktabs`, `enumitem`, `hyperref`, `fontenc`, `inputenc`.

### Switching to BibTeX

`refs.bib` holds the same six references in BibTeX form, for journal submission. To use it,
delete the `thebibliography` block at the end of `main.tex` and put in its place

```latex
\bibliographystyle{amsplain}
\bibliography{refs}
```

then run `pdflatex -> bibtex -> pdflatex -> pdflatex`.

## Lint performed instead of a compile

`main.tex` was checked mechanically (script kept in the session scratchpad) for:

| check | result |
|---|---|
| non-ASCII characters anywhere in the file | 0 (all unicode from the `.md` sources converted to macros) |
| `\begin`/`\end` environment nesting | balanced, 0 errors |
| brace balance (escapes and comments skipped) | final depth 0 |
| inline `$...$` parity | 10 lines with odd counts, all of them math spanning two source lines; every pair sums to even |
| `\[` vs `\]` | 37 / 37 |
| duplicate `\label`s | none |
| `\ref`/`\eqref` with no matching label | none |
| `\cite` with no matching `\bibitem` | none; all 6 bibitems are cited |
| macros used but never defined | none outside the standard LaTeX/amsmath set |

Unused-but-harmless: the macro `\nn` is defined and never used; the label `sec:intro` is
never referenced.

## Files

- `main.tex` — the paper (article body plus Appendix A, the full eleven-variable case analysis).
- `refs.bib` — BibTeX version of the bibliography (not needed for a plain compile).
- `BUILD.md` — this file.

## Compiled 2026-09-13
Tectonic 0.17.0 installed via `scoop install tectonic`. Build: `tectonic -X compile main.tex` in this folder (exit 0, PDF produced; fontconfig warning is harmless).
