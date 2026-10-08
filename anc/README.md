# Ancillary files

The certificate and the four checking programs of the paper (Appendix, and the
SHA-256 table there). Each program runs with Python 3 and no arguments, and reads
`cert_leaves_tail.jsonl` from this directory.

| file | role |
|---|---|
| `cert_leaves_tail.jsonl` | the exact rational Farkas certificate: 8192 cells, 10,820 leaves |
| `verify_712_independent.py` | primary verifier; also checks the witnesses and runs four corruption smoke tests |
| `verify_cert_tail_independent.py` | second verifier, sharing no code with the first |
| `check_stability_constant.py` | the stability constant 18/7; reads the multipliers only |
| `blind_fourth/verify_blind_third.py` | reconstruction of every row from the displayed formulas |
| `leaf_stats.py` | leaf statistics used in the tables; not a validity check |
| `output/` | recorded standard output of the four checking programs |

    python3 verify_712_independent.py
    python3 verify_cert_tail_independent.py
    python3 check_stability_constant.py
    python3 blind_fourth/verify_blind_third.py
