"""
Tests for Sigmatics to Multiplicity bridge.
"""

import pytest
from multiplicity_core.sigmatics_bridge import (
    WordType,
    SigmaticsWord,
    MultiplicityWord,
    classify_word,
    extract_pi_atoms,
    reorder_pi_first,
    compile_word,
    compile_sigmatics_to_multiplicity,
    bridge_compile,
)


# ============================================================================
# Test Word Classification
# ============================================================================

def test_classify_phase_word():
    """Test classification of phase control words."""
    word = classify_word("phase[h₂=0]")
    assert word.type == WordType.PHASE
    assert word.name == "phase"
    assert word.params["h2"] == 0
    
    word = classify_word("phase[h₂=2]")
    assert word.params["h2"] == 2


def test_classify_generator_words():
    """Test classification of generator words."""
    # Without modality
    word = classify_word("evaluate")
    assert word.type == WordType.GENERATOR
    assert word.name == "evaluate"
    assert word.params == {}
    
    # With modality
    word = classify_word("mark[d=0]")
    assert word.type == WordType.GENERATOR
    assert word.name == "mark"
    assert word.params["d"] == 0
    
    word = classify_word("copy[d=1]")
    assert word.name == "copy"
    assert word.params["d"] == 1


def test_classify_transform_words():
    """Test classification of transform words."""
    # Rotate
    word = classify_word("→ρ[1]")
    assert word.type == WordType.ROTATE
    assert word.params["q"] == 1
    assert word.params["dir"] == "→"
    
    word = classify_word("←ρ[2]")
    assert word.params["q"] == 2
    assert word.params["dir"] == "←"
    
    # Mirror
    word = classify_word("~")
    assert word.type == WordType.MIRROR


# ============================================================================
# Test Π-First Reduction
# ============================================================================

def test_extract_pi_atoms():
    """Test extraction of Π-atoms from word list."""
    words = [
        classify_word("phase[h₂=0]"),
        classify_word("mark[d=0]"),
        classify_word("evaluate"),
        classify_word("copy[d=1]"),
        classify_word("→ρ[1]"),
    ]
    
    pi_atoms, other = extract_pi_atoms(words)
    
    # Π-atoms should be generators with modality
    assert len(pi_atoms) == 2
    assert pi_atoms[0].name == "mark"
    assert pi_atoms[1].name == "copy"
    
    # Others should include phase, evaluate, rotate
    assert len(other) == 3
    assert other[0].type == WordType.PHASE
    assert other[1].name == "evaluate"
    assert other[2].type == WordType.ROTATE


def test_reorder_pi_first():
    """Test Π-first reordering."""
    words = [
        classify_word("phase[h₂=0]"),
        classify_word("mark[d=0]"),
        classify_word("evaluate"),
        classify_word("copy[d=1]"),
    ]
    
    reordered = reorder_pi_first(words)
    
    # First two should be Π-atoms
    assert len(reordered) == 4
    assert reordered[0].name == "mark"
    assert reordered[1].name == "copy"
    # Then others in original order
    assert reordered[2].type == WordType.PHASE
    assert reordered[3].name == "evaluate"


# ============================================================================
# Test Word Compilation
# ============================================================================

def test_compile_phase_word():
    """Test compilation of phase control."""
    word = classify_word("phase[h₂=1]")
    mult = compile_word(word)
    
    assert mult.opcode == "SET_QUADRANT"
    assert mult.args == [1]
    assert mult.metadata["source"] == "phase"


def test_compile_generator_words():
    """Test compilation of generator words."""
    # Without modality
    word = classify_word("evaluate")
    mult = compile_word(word)
    assert mult.opcode == "EVALUATE"
    assert mult.args == []
    
    # With modality
    word = classify_word("mark[d=0]")
    mult = compile_word(word)
    assert mult.opcode == "MARK"
    assert mult.args == [0]
    assert mult.metadata["modality"] == 0


def test_compile_transform_words():
    """Test compilation of transforms."""
    # Rotate
    word = classify_word("→ρ[2]")
    mult = compile_word(word)
    assert mult.opcode == "ROTATE"
    assert mult.args == [2]
    
    # Mirror
    word = classify_word("~")
    mult = compile_word(word)
    assert mult.opcode == "MIRROR"


# ============================================================================
# Test Full Compilation Pipeline
# ============================================================================

def test_compile_simple_sequence():
    """Test compilation of a simple word sequence."""
    sigmatics_words = ["phase[h₂=0]", "evaluate"]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=False)
    
    assert len(result) == 2
    assert result[0].opcode == "SET_QUADRANT"
    assert result[1].opcode == "EVALUATE"


def test_compile_with_pi_first():
    """Test compilation with Π-first reduction."""
    sigmatics_words = [
        "phase[h₂=0]",
        "mark[d=0]",
        "evaluate",
        "copy[d=1]",
    ]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=True)
    
    # Π-atoms should be first
    assert len(result) == 4
    assert result[0].opcode == "MARK"
    assert result[1].opcode == "COPY"
    assert result[2].opcode == "SET_QUADRANT"
    assert result[3].opcode == "EVALUATE"


def test_compile_without_pi_first():
    """Test compilation without Π-first reduction."""
    sigmatics_words = [
        "phase[h₂=0]",
        "mark[d=0]",
        "evaluate",
    ]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=False)
    
    # Order should be preserved
    assert len(result) == 3
    assert result[0].opcode == "SET_QUADRANT"
    assert result[1].opcode == "MARK"
    assert result[2].opcode == "EVALUATE"


# ============================================================================
# Test Bridge API
# ============================================================================

def test_bridge_compile():
    """Test main bridge compilation function."""
    sigmatics_words = [
        "phase[h₂=0]",
        "mark[d=0]",
        "evaluate",
    ]
    
    result = bridge_compile(sigmatics_words, apply_pi_first=True)
    
    assert result.sigmatics_words == sigmatics_words
    assert len(result.multiplicity_words) == 3
    assert result.pi_first_applied == True
    
    # Check summary generation
    summary = result.summary()
    assert "Compilation Summary" in summary
    assert "phase[h₂=0]" in summary


def test_bridge_compile_with_metadata():
    """Test bridge compilation with metadata."""
    sigmatics_words = ["evaluate"]
    metadata = {"source": "test", "version": "0.1"}
    
    result = bridge_compile(sigmatics_words, metadata=metadata)
    
    assert result.metadata == metadata


# ============================================================================
# Test Example Sequences
# ============================================================================

def test_example_sequential_composition():
    """Test example from Sigmatics: sequential composition."""
    # Example: "copy@c05 . merge@c13"
    # Operational backend produces: ["merge[d=1]", "copy[d=0]"]
    sigmatics_words = ["merge[d=1]", "copy[d=0]"]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=True)
    
    # With Π-first: both are Π-atoms, so order is preserved
    assert len(result) == 2
    assert result[0].opcode == "MERGE"
    assert result[0].args == [1]
    assert result[1].opcode == "COPY"
    assert result[1].args == [0]


def test_example_with_transforms():
    """Test example with transforms."""
    # Example: "R+1@ evaluate@c21"
    # Operational backend: ["→ρ[1]", "phase[h₂=1]", "evaluate", "←ρ[1]"]
    sigmatics_words = ["→ρ[1]", "phase[h₂=1]", "evaluate", "←ρ[1]"]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=False)
    
    assert len(result) == 4
    assert result[0].opcode == "ROTATE"
    assert result[1].opcode == "SET_QUADRANT"
    assert result[2].opcode == "EVALUATE"
    assert result[3].opcode == "ROTATE"


def test_example_mixed_operations():
    """Test mixed operations with Π-first."""
    sigmatics_words = [
        "phase[h₂=0]",
        "copy[d=0]",
        "evaluate",
        "mark[d=2]",
        "→ρ[1]",
    ]
    
    result = compile_sigmatics_to_multiplicity(sigmatics_words, apply_pi_first=True)
    
    # Π-atoms (copy, mark) should be first
    assert len(result) == 5
    assert result[0].opcode == "COPY"
    assert result[1].opcode == "MARK"
    # Then others in order
    assert result[2].opcode == "SET_QUADRANT"
    assert result[3].opcode == "EVALUATE"
    assert result[4].opcode == "ROTATE"
