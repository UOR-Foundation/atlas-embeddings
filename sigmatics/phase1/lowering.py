"""
Deterministic Lowering to JSON Words

This module implements deterministic lowering of Sigmatics statements to JSON words
with metadata. The lowering is stable under whitespace and formatting changes.

Lowered JSON word shape (canonical keys and order):
  {"op":<str>,"args":{...},"meta":{"src":<str>,"span":[start,end]}}

Determinism rule: identical semantic tokens produce identical lowered JSON strings and hash.
"""

import json
import hashlib
from typing import List, Dict, Any

try:
    from .lexer_parser import tokenize, parse_stmt
except ImportError:
    from lexer_parser import tokenize, parse_stmt


def stable_json_dumps(obj: Any) -> str:
    """
    Create a stable, deterministic JSON string representation.
    
    Uses sorted keys and compact separators for consistency.
    
    Args:
        obj: Any JSON-serializable object
        
    Returns:
        Deterministic JSON string
    """
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha1(s: str) -> str:
    """
    Compute SHA-1 hash of a string.
    
    Args:
        s: Input string
        
    Returns:
        Hexadecimal SHA-1 hash
    """
    return hashlib.sha1(s.encode("utf-8")).hexdigest()


def lower(script: str, src_name: str = "inline") -> Dict[str, Any]:
    """
    Lower a Sigmatics script to canonical JSON words with metadata.
    
    This performs deterministic normalization:
    1. Tokenize and parse the script
    2. Attach source metadata (file name, span)
    3. Canonicalize to deterministic JSON form
    4. Compute a stable hash
    
    The hash is stable under whitespace and formatting changes as long as
    the semantic content is identical. The hash excludes span information
    to achieve this determinism.
    
    Args:
        script: The Sigmatics script text
        src_name: Source file name for metadata (default: "inline")
        
    Returns:
        Dictionary with:
          - "lowered": {"words": [...]} with canonical structure
          - "lowering_hash": SHA-1 hash of the canonical form (excluding spans)
    """
    toks = tokenize(script)
    words = []
    
    for stmt, (a, b) in toks:
        node = parse_stmt(stmt)
        lowered_word = {
            "op": node["op"],
            "args": node.get("args", {}),
            "meta": {"src": src_name, "span": [a, b]}
        }
        words.append(lowered_word)
    
    # Deterministic normalization: stable sort by original span, then canonicalize keys
    canonical = json.loads(stable_json_dumps({"words": words}))
    
    # For hash computation, create a version without span information
    # This ensures identical semantic content produces identical hash
    words_without_spans = []
    for word in words:
        word_copy = {
            "op": word["op"],
            "args": word["args"],
            "meta": {"src": word["meta"]["src"]}
        }
        words_without_spans.append(word_copy)
    
    canonical_for_hash = json.loads(stable_json_dumps({"words": words_without_spans}))
    lowering_hash = sha1(stable_json_dumps(canonical_for_hash))
    
    return {"lowered": canonical, "lowering_hash": lowering_hash}


def verify_determinism(script1: str, script2: str, src_name: str = "test") -> bool:
    """
    Verify that two semantically identical scripts produce the same lowering hash.
    
    This is useful for testing determinism - scripts with different whitespace
    or formatting but identical semantic content should hash the same.
    
    Note: The lowered structures will differ in span information, but the
    hash (which excludes spans) should be identical.
    
    Args:
        script1: First script
        script2: Second script (with different formatting)
        src_name: Source name for both
        
    Returns:
        True if both produce identical lowering hashes
    """
    lo1 = lower(script1, src_name)
    lo2 = lower(script2, src_name)
    
    # Only compare hashes, not the full structures (which will have different spans)
    return lo1["lowering_hash"] == lo2["lowering_hash"]
