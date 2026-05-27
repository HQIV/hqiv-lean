# LieBracketCell — sources not in this paper-reference mirror

This bundle intentionally **does not** copy the 784 modules `R{i}C{j}.lean` nor the 28 `Row{k}Summary.lean` files under `Hqiv/LieBracketCell/`. Each cell proof unfolds real matrix literals and runs `norm_num` on 64 entrywise goals; with Lake’s default parallelism, total resident memory can exceed **100GB**.

**From this mirror (supported):** `lake build HQIVPaperClaims` — manuscript symbolic interface; does not import LieBracketCell.

**Full matrix Lie closure (`HQIVSO8Closure`):** use a **complete** checkout of the repository (all `Hqiv/LieBracketCell/*.lean` present) and run:

```bash
scripts/build_hqiv_so8_closure_lowmem.sh
```

That sets `LEAN_NUM_THREADS=1` and `lake build … -j 1` so jobs run sequentially.
