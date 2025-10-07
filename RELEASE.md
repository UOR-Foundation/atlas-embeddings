# Release Process

## Creating a New Release

1. **Update version** in `Cargo.toml`
2. **Update CHANGELOG.md** with release notes
3. **Run verification**: `make verify`
4. **Commit changes**: `git commit -m "chore: bump version to X.Y.Z"`
5. **Create git tag**: `git tag -a vX.Y.Z -m "Release vX.Y.Z"`
6. **Push with tags**: `git push origin main --tags`

## After First Release (v0.1.0)

### Update Zenodo DOI Badge

Once Zenodo generates the DOI for your first release:

1. Go to https://zenodo.org and find your repository
2. Copy the **concept DOI** (e.g., `10.5281/zenodo.1234567`)
3. Update the DOI badge in `README.md`:

   Replace:
   ```markdown
   [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.XXXXXXX.svg)](https://doi.org/10.5281/zenodo.XXXXXXX)
   ```

   With:
   ```markdown
   [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.1234567.svg)](https://doi.org/10.5281/zenodo.1234567)
   ```

4. Update the DOI in `src/lib.rs` citation section
5. Commit the changes:
   ```bash
   git add README.md src/lib.rs
   git commit -m "docs: add Zenodo DOI badge"
   git push origin main
   ```

### Publishing to crates.io

1. **Login to crates.io**: `cargo login`
2. **Publish**: `cargo publish --dry-run` (test first)
3. **Actually publish**: `cargo publish`

## Automatic DOI Generation

- Zenodo automatically generates a new DOI for each GitHub release
- The **concept DOI** always points to the latest version
- Version-specific DOIs allow citing exact versions
