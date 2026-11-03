# A primitive-ratio cut and a 7/12 bound for the abc exceptional set

Ruiyi Zhang

DOI: [10.5281/zenodo.23247752](https://doi.org/10.5281/zenodo.23247752)

Let `N_1(X)` count the abc triples `(a,b,c)` in `[1,X]^3` with `rad(abc) < c`.
The manuscript proves

    N_1(X) <<_eps X^{7/12+eps}.

The previous bound proved in full was `X^{13/20+eps}`. The proof keeps the anatomic
reduction of Bernert, Browning, Lichtman and Teräväinen and adds two exact rows per side
for the root classes of index at least seven, and a cut. The cut fixes all but two
coprime products on two sides; the remaining pairs are primitive points of a lattice whose
determinant is a product of roots on the third side. This gives 1,560,195 further
inequalities. An exact Farkas certificate over 8192 cells and 10,820 leaves gives the
exponent `7/12` for the box count; on each leaf the multipliers sum to at most `18/7`.

## Contents

- `main.tex`, `main.pdf` (16 pages)
- `anc/` - the certificate and the four checking programs whose SHA-256 values are
  printed in the paper, with their recorded outputs. See `anc/README.md`.
- `SHA256SUMS`

## Build

    pdflatex main.tex
    pdflatex main.tex

## Checks

    cd anc && python3 verify_712_independent.py

## Citation

Ruiyi Zhang, *A primitive-ratio cut and a 7/12 bound for the abc exceptional set*, preprint, Zenodo, 2026. https://doi.org/10.5281/zenodo.23247752

```bibtex
@misc{zhang2026exceptional,
  author    = {Zhang, Ruiyi},
  title     = {A primitive-ratio cut and a 7/12 bound for the abc exceptional set},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.23247752},
  url       = {https://doi.org/10.5281/zenodo.23247752}
}
```
