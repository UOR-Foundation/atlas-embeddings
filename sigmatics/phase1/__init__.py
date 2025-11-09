"""
Phase 1 — Front end and compiler (Sigmatics → JSON → Multiplicity)

This package implements:
- Lexer/Parser/Normalizer for a minimal Sigmatics DSL
- Deterministic lowering to JSON words + meta
- JSON Schemas for SigmaticsWord, MultiplicityWord, Program
- Minimal compiler with Π-first and admissibility checks
- Obligations emitted for UNPROVEN policies

All policies are marked UNPROVEN until mathematically verified.
"""

from .lexer_parser import tokenize, parse_stmt, parse
from .lowering import lower, stable_json_dumps, sha1, verify_determinism
from .policies import Policies, admissible, N
from .compiler import compile_words, compile_program

__all__ = [
    # Lexer/Parser
    "tokenize",
    "parse_stmt",
    "parse",
    
    # Lowering
    "lower",
    "stable_json_dumps",
    "sha1",
    "verify_determinism",
    
    # Policies
    "Policies",
    "admissible",
    "N",
    
    # Compiler
    "compile_words",
    "compile_program",
]

__version__ = "0.1.0"
