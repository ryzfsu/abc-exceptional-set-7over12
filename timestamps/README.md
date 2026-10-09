# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
970653 (2026-10-09 15:43:29 UTC).

| file | SHA-256 |
|---|---|
| `abc-exceptional-set-7over12-v1.pdf` | `2ba17bd960a0d90da61fc47d5a977407c2cd98ccda8d3a0329438e50f56cfa58` |
| `abc-exceptional-set-7over12-v1.tar.gz` | `6f685473ea846a5cc54efd42f742c4d947ebbae4c927e668ad27b285139082da` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
