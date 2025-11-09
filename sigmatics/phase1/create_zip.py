#!/usr/bin/env python3
"""
Package Phase 1 artifacts into a ZIP file.

This script packages all Phase 1 implementation files and artifacts
into a distributable ZIP archive.
"""

import os
import zipfile
from pathlib import Path


def create_phase1_zip():
    """Create ZIP archive of Phase 1 artifacts."""
    
    phase1_dir = Path(__file__).parent
    zip_path = phase1_dir / "phase1_apex_v0.zip"
    
    # Files to include
    include_patterns = [
        "*.py",
        "*.sig",
        "*.md",
        ".gitignore",
        "schemas/*.json",
        "artifacts/*.json",
    ]
    
    # Collect files
    files_to_zip = []
    
    # Python files
    for py_file in phase1_dir.glob("*.py"):
        if "__pycache__" not in str(py_file):
            files_to_zip.append(py_file)
    
    # Sigmatics script
    for sig_file in phase1_dir.glob("*.sig"):
        files_to_zip.append(sig_file)
    
    # Documentation
    for md_file in phase1_dir.glob("*.md"):
        files_to_zip.append(md_file)
    
    # .gitignore
    gitignore = phase1_dir / ".gitignore"
    if gitignore.exists():
        files_to_zip.append(gitignore)
    
    # Schemas
    schemas_dir = phase1_dir / "schemas"
    if schemas_dir.exists():
        for schema_file in schemas_dir.glob("*.json"):
            files_to_zip.append(schema_file)
    
    # Artifacts
    artifacts_dir = phase1_dir / "artifacts"
    if artifacts_dir.exists():
        for artifact_file in artifacts_dir.glob("*.json"):
            files_to_zip.append(artifact_file)
    
    # Create ZIP
    print(f"Creating ZIP archive: {zip_path}")
    print(f"Including {len(files_to_zip)} files...")
    
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for file_path in sorted(files_to_zip):
            arcname = file_path.relative_to(phase1_dir)
            zf.write(file_path, arcname=arcname)
            print(f"  + {arcname}")
    
    # Get ZIP info
    zip_size = zip_path.stat().st_size
    
    print(f"\n✓ ZIP created: {zip_path}")
    print(f"✓ Size: {zip_size:,} bytes ({zip_size/1024:.1f} KB)")
    print(f"✓ Files: {len(files_to_zip)}")
    
    return zip_path, len(files_to_zip), zip_size


if __name__ == "__main__":
    create_phase1_zip()
