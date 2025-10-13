!!! warning "Computational evidence"
    The content below is evidence produced by exact-arithmetic programs. It is **not** a proof.

# E1–E3 validation

**E1.** Inner-product multiset for the 96-set.  
**E2.** +1 adjacency: |E|, degree min/max, average 65/3.  
**E3.** Integral Cartans, Dynkin identification, and Weyl orders.

Artifacts:
- `artifacts/phase7/validation.json`
- `artifacts/phase7/validation.sha256`

Reproduce:
```bash
python bin/validate.py --iota data/iota_96.json --out artifacts/phase7
```
