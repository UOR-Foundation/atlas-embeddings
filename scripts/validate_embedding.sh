#!/bin/bash
# Quick validation of the mirror symmetry invariant

set -e

echo "======================================"
echo "Mirror Symmetry Invariant Validation"
echo "======================================"
echo ""

echo "Running decisive test: 4560 pair adjacency check..."
cargo test test_mirror_symmetry_invariant_all_pairs -- --nocapture

echo ""
echo "Running supplementary embedding tests..."
cargo test --test atlas_e8_embedding --quiet

echo ""
echo "======================================"
echo "✅ VALIDATION COMPLETE"
echo "======================================"
echo ""
echo "The Atlas→E8 embedding is FUNCTIONAL."
echo "All 4560 pairs satisfy the mirror symmetry invariant."
echo ""
echo "This proves the stack is executable mathematics,"
echo "not documentary fiction."
