"""
Sigmatics to Multiplicity Bridge: Π-First Reduction Compiler

This module implements the compilation bridge from Sigmatics words (SGA elements)
to Multiplicity words with Π-first reduction strategy.

The bridge:
1. Takes Sigmatics operational words (from SGA evaluator)
2. Applies Π-first reduction (product projectors processed first)
3. Compiles to Multiplicity runtime instructions
4. Maintains index map compatibility with Phase 0 constraints

Status: UNPROVEN - This is a minimal, testable bridge implementation.
"""

from __future__ import annotations
from typing import List, Tuple, Optional, Dict, Any
from dataclasses import dataclass
from enum import Enum


# ============================================================================
# Word Types
# ============================================================================

class WordType(Enum):
    """Types of words in the compilation."""
    PHASE = "phase"          # Phase control (h₂ quadrant)
    GENERATOR = "generator"  # Atlas generator (mark, copy, etc.)
    ROTATE = "rotate"        # Rotate transform
    TWIST = "twist"          # Twist/march transform
    MIRROR = "mirror"        # Mirror transform
    PI_ATOM = "pi_atom"      # Π-atom (product projector)
    MULTIPLICITY = "mult"    # Multiplicity operation


@dataclass
class SigmaticsWord:
    """
    A word from Sigmatics operational backend.
    
    Examples:
      - "phase[h₂=0]"
      - "evaluate"
      - "→ρ[1]" (rotate)
      - "mark[d=0]"
    """
    type: WordType
    name: str
    params: Dict[str, Any]
    
    def __str__(self) -> str:
        if self.params:
            param_str = ", ".join(f"{k}={v}" for k, v in self.params.items())
            return f"{self.name}[{param_str}]"
        return self.name


@dataclass
class MultiplicityWord:
    """
    A word in the Multiplicity runtime.
    
    These are the executable operations in the runtime with
    Π-atom updates processed first (Π-first reduction).
    """
    opcode: str
    args: List[Any]
    metadata: Dict[str, Any]
    
    def __str__(self) -> str:
        args_str = ", ".join(str(a) for a in self.args)
        return f"{self.opcode}({args_str})"


# ============================================================================
# Π-First Reduction
# ============================================================================

def classify_word(word_str: str) -> SigmaticsWord:
    """
    Classify a Sigmatics word string into a structured SigmaticsWord.
    
    Args:
        word_str: Raw word string from Sigmatics operational backend
    
    Returns:
        SigmaticsWord with type, name, and parameters
    """
    # Parse phase control
    if word_str.startswith("phase["):
        # Extract h₂ parameter
        import re
        match = re.search(r"h₂=(\d+)", word_str)
        h2 = int(match.group(1)) if match else 0
        return SigmaticsWord(
            type=WordType.PHASE,
            name="phase",
            params={"h2": h2}
        )
    
    # Parse generators with modality
    generators = ["mark", "copy", "swap", "merge", "split", "quote", "evaluate"]
    for gen in generators:
        if word_str.startswith(gen):
            import re
            match = re.search(r"d=(\d+)", word_str)
            d = int(match.group(1)) if match else None
            params = {"d": d} if d is not None else {}
            return SigmaticsWord(
                type=WordType.GENERATOR,
                name=gen,
                params=params
            )
    
    # Parse rotate
    if "→ρ[" in word_str or "←ρ[" in word_str:
        import re
        match = re.search(r"[→←]ρ\[(\d+)\]", word_str)
        q = int(match.group(1)) if match else 1
        return SigmaticsWord(
            type=WordType.ROTATE,
            name="rotate",
            params={"q": q, "dir": "→" if "→" in word_str else "←"}
        )
    
    # Parse twist
    if "twist" in word_str.lower():
        return SigmaticsWord(
            type=WordType.TWIST,
            name="twist",
            params={}
        )
    
    # Parse mirror
    if "~" in word_str or "mirror" in word_str.lower():
        return SigmaticsWord(
            type=WordType.MIRROR,
            name="mirror",
            params={}
        )
    
    # Default: treat as generic operation
    return SigmaticsWord(
        type=WordType.GENERATOR,
        name=word_str,
        params={}
    )


def extract_pi_atoms(words: List[SigmaticsWord]) -> Tuple[List[SigmaticsWord], List[SigmaticsWord]]:
    """
    Separate Π-atoms from other words (Π-first reduction step 1).
    
    Π-atoms are product projectors that should be processed first
    in the Π-first reduction strategy.
    
    Args:
        words: List of Sigmatics words
    
    Returns:
        (pi_atoms, other_words) tuple
    """
    # For now, identify Π-atoms by heuristic:
    # - Generators with modality parameters are potential Π-atoms
    # - Phase controls are not Π-atoms
    # - Transforms are not Π-atoms
    
    pi_atoms = []
    other_words = []
    
    for word in words:
        if word.type == WordType.GENERATOR and "d" in word.params:
            # Generator with modality → likely a Π-atom
            pi_atoms.append(word)
        else:
            other_words.append(word)
    
    return pi_atoms, other_words


def reorder_pi_first(words: List[SigmaticsWord]) -> List[SigmaticsWord]:
    """
    Reorder words to process Π-atoms first (Π-first reduction).
    
    Strategy:
    1. Extract all Π-atoms
    2. Keep other words in original order
    3. Return: [Π-atoms...] + [other_words...]
    
    Args:
        words: List of Sigmatics words
    
    Returns:
        Reordered list with Π-atoms first
    """
    pi_atoms, other_words = extract_pi_atoms(words)
    return pi_atoms + other_words


# ============================================================================
# Compilation
# ============================================================================

def compile_word(word: SigmaticsWord) -> MultiplicityWord:
    """
    Compile a single Sigmatics word to a Multiplicity word.
    
    Args:
        word: Sigmatics word
    
    Returns:
        Multiplicity word
    """
    if word.type == WordType.PHASE:
        # Phase control → set quadrant
        return MultiplicityWord(
            opcode="SET_QUADRANT",
            args=[word.params.get("h2", 0)],
            metadata={"source": "phase"}
        )
    
    elif word.type == WordType.GENERATOR:
        # Generator → runtime operation
        # Map generator name to opcode
        opcode_map = {
            "mark": "MARK",
            "copy": "COPY",
            "swap": "SWAP",
            "merge": "MERGE",
            "split": "SPLIT",
            "quote": "QUOTE",
            "evaluate": "EVALUATE"
        }
        opcode = opcode_map.get(word.name, word.name.upper())
        
        # Add modality as argument if present
        args = []
        if "d" in word.params:
            args.append(word.params["d"])
        
        return MultiplicityWord(
            opcode=opcode,
            args=args,
            metadata={"modality": word.params.get("d")}
        )
    
    elif word.type == WordType.ROTATE:
        # Rotate transform
        return MultiplicityWord(
            opcode="ROTATE",
            args=[word.params.get("q", 1)],
            metadata={"direction": word.params.get("dir", "→")}
        )
    
    elif word.type == WordType.TWIST:
        # Twist/march transform
        return MultiplicityWord(
            opcode="TWIST",
            args=[],
            metadata={}
        )
    
    elif word.type == WordType.MIRROR:
        # Mirror transform
        return MultiplicityWord(
            opcode="MIRROR",
            args=[],
            metadata={}
        )
    
    else:
        # Generic operation
        return MultiplicityWord(
            opcode="OP",
            args=[word.name],
            metadata={}
        )


def compile_sigmatics_to_multiplicity(
    sigmatics_words: List[str],
    apply_pi_first: bool = True
) -> List[MultiplicityWord]:
    """
    Compile Sigmatics operational words to Multiplicity words.
    
    Pipeline:
    1. Classify each word string → SigmaticsWord
    2. (Optional) Apply Π-first reduction to reorder
    3. Compile each word → MultiplicityWord
    
    Args:
        sigmatics_words: List of word strings from Sigmatics operational backend
        apply_pi_first: If True, apply Π-first reduction reordering
    
    Returns:
        List of Multiplicity words ready for runtime
    """
    # Step 1: Classify words
    classified = [classify_word(w) for w in sigmatics_words]
    
    # Step 2: Apply Π-first reduction if requested
    if apply_pi_first:
        classified = reorder_pi_first(classified)
    
    # Step 3: Compile to Multiplicity words
    compiled = [compile_word(w) for w in classified]
    
    return compiled


# ============================================================================
# Bridge API
# ============================================================================

@dataclass
class CompilationResult:
    """Result of Sigmatics → Multiplicity compilation."""
    sigmatics_words: List[str]
    multiplicity_words: List[MultiplicityWord]
    pi_first_applied: bool
    metadata: Dict[str, Any]
    
    def summary(self) -> str:
        """Generate human-readable summary."""
        lines = []
        lines.append("Compilation Summary")
        lines.append("=" * 60)
        lines.append(f"Input: {len(self.sigmatics_words)} Sigmatics words")
        lines.append(f"Output: {len(self.multiplicity_words)} Multiplicity words")
        lines.append(f"Π-first reduction: {'Applied' if self.pi_first_applied else 'Not applied'}")
        lines.append("")
        lines.append("Sigmatics words:")
        for w in self.sigmatics_words:
            lines.append(f"  {w}")
        lines.append("")
        lines.append("Multiplicity words:")
        for w in self.multiplicity_words:
            lines.append(f"  {w}")
        lines.append("=" * 60)
        return "\n".join(lines)


def bridge_compile(
    sigmatics_words: List[str],
    apply_pi_first: bool = True,
    metadata: Optional[Dict[str, Any]] = None
) -> CompilationResult:
    """
    Main bridge compilation function.
    
    Compiles Sigmatics operational words to Multiplicity runtime words
    with optional Π-first reduction.
    
    Args:
        sigmatics_words: List of word strings from Sigmatics
        apply_pi_first: Whether to apply Π-first reduction
        metadata: Optional metadata to attach
    
    Returns:
        CompilationResult with compilation details
    """
    multiplicity_words = compile_sigmatics_to_multiplicity(
        sigmatics_words,
        apply_pi_first=apply_pi_first
    )
    
    return CompilationResult(
        sigmatics_words=sigmatics_words,
        multiplicity_words=multiplicity_words,
        pi_first_applied=apply_pi_first,
        metadata=metadata or {}
    )


__all__ = [
    # Types
    "WordType",
    "SigmaticsWord",
    "MultiplicityWord",
    "CompilationResult",
    
    # Classification
    "classify_word",
    
    # Π-first reduction
    "extract_pi_atoms",
    "reorder_pi_first",
    
    # Compilation
    "compile_word",
    "compile_sigmatics_to_multiplicity",
    "bridge_compile",
]
