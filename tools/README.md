# Tools Directory

This directory contains utility scripts and tools for the Atlas Hologram project.

## copilot_repo_setup.md

A comprehensive bootstrap script that reorganizes the repository into a clean monorepo structure.

### Purpose

This script:
- Organizes the repository into Atlas, Embeddings, and Sigmatics components
- Moves Atlas core files from scattered locations into a unified `atlas/` directory
- Creates stub directories and documentation for Embeddings and Sigmatics
- Updates root documentation and build configuration
- Patches build scripts for the new structure

### Usage

**Basic usage:**
```bash
bash tools/copilot_repo_setup.md
```

**Dry-run (see what would be done without making changes):**
```bash
bash tools/copilot_repo_setup.md --dry-run
```

**Skip tests after setup:**
```bash
bash tools/copilot_repo_setup.md --no-test
```

**Combine options:**
```bash
bash tools/copilot_repo_setup.md --dry-run --no-test
```

### What It Does

1. **Creates Directory Structure:**
   - `atlas/` - Core C library with src/, include/, tests/, tools/, bindings/
   - `embeddings/` - Data embedding layer (stubs)
   - `sigmatics/` - Symbolic algebra layer (stubs)

2. **Moves Files (Git-Aware):**
   - Moves `atlas_core/src/*` to `atlas/src/`
   - Moves `atlas_core/include/*` to `atlas/include/`
   - Copies test files to `atlas/tests/`
   - Copies verify_bridge.sh to `atlas/tools/`
   - Copies bindings to `atlas/bindings/`

3. **Handles Artifacts:**
   - Copies optional artifacts (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
   - Places them in `atlas/artifacts/`
   - Creates example files if originals are missing

4. **Updates Documentation:**
   - Creates `atlas/README.md` with component overview
   - Creates `embeddings/README.md` with stub documentation
   - Creates `sigmatics/README.md` with stub documentation
   - Updates root `README.md` with monorepo structure

5. **Updates Build System:**
   - Creates `Makefile.atlas` with atlas-build, atlas-test, atlas-cert targets
   - Updates `atlas/tools/verify_bridge.sh` for new paths
   - Creates `.github/workflows/atlas_bridge.yml` for CI

6. **Fixes References:**
   - Updates test file include paths
   - Patches verify_bridge.sh to work from new location

### Features

- **Idempotent:** Safe to run multiple times, only creates/moves what's missing
- **Git-Aware:** Uses `git mv` for tracked files, preserving history
- **Colored Output:** Clear status messages with color coding
- **Dry-Run Mode:** Preview changes before applying them
- **Error Handling:** Exits on error, validates operations

### After Running

1. Review the changes:
   ```bash
   git status
   ```

2. Test the build:
   ```bash
   make -f Makefile.atlas atlas-test
   ```

3. Verify certificate generation:
   ```bash
   cat bridge_cert.json
   ```

4. Commit the reorganization:
   ```bash
   git add -A
   git commit -m "Reorganize monorepo structure"
   ```

### Notes

- The script is idempotent - safe to run multiple times
- Existing files are never overwritten
- Build artifacts are excluded via .gitignore
- Original files are moved (not copied) when tracked by git
- Backup files are not created (to avoid clutter)

## verify_bridge.sh

Located in `atlas/tools/verify_bridge.sh` after running the bootstrap script.

This script:
- Detects BLAS libraries
- Builds the Atlas Bridge library
- Compiles and runs all test suites
- Generates a certificate with metrics verification
- Enforces quality thresholds

See `atlas/tools/verify_bridge.sh` for details.

## Other Tools

- `claims_guard.py` - Validates documentation claims
- `docs_lint.py` - Lints documentation
- `terminology_lint.py` - Checks terminology consistency
- `manifest.py` - Manages project manifest
- `fracfmt.py` - Formats fractional values
