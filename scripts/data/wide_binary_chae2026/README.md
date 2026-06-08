# Chae (2026) wide-binary clean sample

36-system catalog used in the gravitational-anomaly debate:

- Chae et al. (2026): [arXiv:2601.21728](https://arxiv.org/abs/2601.21728) — reports \(\gamma \approx 1.60\) at low acceleration.
- Saad & Ting (2026): [arXiv:2603.11015](https://arxiv.org/abs/2603.11015) — hierarchical 3D forward model; \(\gamma \approx 1.00\) with free semi-major axis, \(\gamma \approx 1.56\) with geometric de-projection only.

Files (copied from [seratsaad/wb3d-gamma](https://github.com/seratsaad/wb3d-gamma)):

| File | Contents |
|------|----------|
| `chae_2026_data.csv` | Masses, RV differences, \(v_{\rm obs}/v_{\rm esc}\), selection flags |
| `chae_2026_gaia.csv` | Gaia DR3 astrometry and per-system \(\Gamma\) posteriors |

HQIV reference system: **chae2026_58** (Gaia `5607190344506642432` / `5607189485513198208`, HARPS RV, \(v_{\rm obs}/v_{\rm esc}\approx 0.35\)).

```bash
PYTHONPATH=scripts python3 scripts/hqiv_wide_binary.py --list-chae
PYTHONPATH=scripts python3 scripts/hqiv_wide_binary.py --full-treatment --chae-id 58
```
