"""
Sigmatics DSL Lexer and Parser

This module implements a lexer and parser for the minimal Sigmatics DSL:

Grammar (single-line statements, ';' terminator; whitespace-insensitive):
  copy
  swap@c_d                 # channels or labels
  ~                        # mirror
  merge
  split@ℓ:type             # example: split@ℓ:int
  mark@{...}               # JSON-like object, e.g. mark@{"p":3,"r":1,"mode":"delta"}
  quote
  evaluate
  rho[k]                   # rotation +k
  tau[k]                   # rotation -k
  mu[p]                    # W^{(p)}_π per policy

Determinism rule: identical semantic tokens produce identical lowered JSON strings and hash.
"""

import re
import json
from typing import List, Tuple, Dict, Any


def tokenize(script: str) -> List[Tuple[str, Tuple[int, int]]]:
    """
    Tokenize a Sigmatics script into statements with span information.
    
    Splits by ';' but keeps spans for each statement for source tracking.
    
    Args:
        script: The Sigmatics script text
        
    Returns:
        List of (statement, (start, end)) tuples
    """
    tokens = []
    start = 0
    
    for m in re.finditer(r";", script):
        end = m.start()
        stmt = script[start:end].strip()
        if stmt:
            tokens.append((stmt, (start, end)))
        start = m.end()
    
    # Handle trailing segment if no semicolon at end
    tail = script[start:].strip()
    if tail:
        tokens.append((tail, (start, len(script))))
    
    return tokens


def parse_stmt(stmt: str) -> Dict[str, Any]:
    """
    Parse a single Sigmatics statement into a structured dictionary.
    
    Args:
        stmt: A single statement string (without semicolon)
        
    Returns:
        Dictionary with "op" and "args" keys
        
    Raises:
        ValueError: If the statement is unrecognized
    """
    s = stmt.strip()
    
    # Normalize unicode greek names to ascii keys
    s = s.replace("ρ", "rho").replace("τ", "tau").replace("μ", "mu")
    
    # Remove extraneous spaces around punctuation
    s = re.sub(r"\s+", "", s)
    
    # Simple operations (no arguments)
    if s == "copy":
        return {"op": "copy", "args": {}}
    if s == "~":
        return {"op": "mirror", "args": {}}
    if s == "merge":
        return {"op": "merge", "args": {}}
    if s == "quote":
        return {"op": "quote", "args": {}}
    if s == "evaluate":
        return {"op": "evaluate", "args": {}}
    
    # swap@c_d
    m = re.match(r"swap@([A-Za-z_][A-Za-z0-9_]*)_([A-Za-z_][A-Za-z0-9_]*)$", s)
    if m:
        return {"op": "swap", "args": {"c": m.group(1), "d": m.group(2)}}
    
    # split@ℓ:type
    m = re.match(r"split@ℓ:([A-Za-z][A-Za-z0-9_]*)$", s)
    if m:
        return {"op": "split", "args": {"ellType": m.group(1)}}
    
    # mark@{...} with JSON payload
    m = re.match(r"mark@(\{.*\})$", s)
    if m:
        try:
            payload = json.loads(m.group(1))
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON payload in mark: {e}")
        return {"op": "mark", "args": {"d": payload}}
    
    # rho[k] - rotation +k
    m = re.match(r"rho\[(\-?\d+)\]$", s)
    if m:
        return {"op": "control", "args": {"kind": "rho", "k": int(m.group(1))}}
    
    # tau[k] - rotation -k
    m = re.match(r"tau\[(\-?\d+)\]$", s)
    if m:
        return {"op": "control", "args": {"kind": "tau", "k": int(m.group(1))}}
    
    # mu[p] - W^{(p)}_π per policy
    m = re.match(r"mu\[(\d+)\]$", s)
    if m:
        return {"op": "control", "args": {"kind": "mu", "p": int(m.group(1))}}
    
    raise ValueError(f"Unrecognized statement: {stmt}")


def parse(script: str) -> List[Dict[str, Any]]:
    """
    Parse a complete Sigmatics script into a list of parsed statements.
    
    Args:
        script: The complete Sigmatics script
        
    Returns:
        List of parsed statement dictionaries
    """
    tokens = tokenize(script)
    return [parse_stmt(stmt) for stmt, _ in tokens]
