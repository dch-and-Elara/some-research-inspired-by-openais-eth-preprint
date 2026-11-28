# Rebuilding the published layout

This directory contains the XeTeX source for reproducing the published layout. The public PDF also received local byline and contribution-statement edits to preserve its existing pagination. The [editable manuscript](../Paper6.tex) uses the standard LaTeX packages. The published layout uses an offline font setup. Place [KaTeX Math Bold Italic, version 0.16.22](https://cdn.jsdelivr.net/npm/katex@0.16.22/dist/fonts/KaTeX_Math-BoldItalic.ttf) beside the typesetting input, then run:

```sh
tectonic Paper6_working.tex
```

The font SHA-256 is `f9377ab0271cda59af24bcffbd46a4d0c8a3572ffafdbb38de2ad5ea7b0d5ee5`. The local build ran the XeTeX and XDV-to-PDF stages through Tectonic. Engine, package and metadata differences can affect the resulting PDF hash. Keep the [evidence catalogue](../EVIDENCE_CATALOG.md) beside the distributed PDF for its relative links.
