"""
Phase 3 — Validation & KPIs (Sigmatics × Multiplicity)

This module validates unit properties, round-trip integrity, and computes KPIs
for the Sigmatics × Multiplicity pipeline.

Key features:
- Unit property validation (idempotence, non-commutation, rotation closure)
- Round-trip integrity checking
- KPI computation (resonance uplift, determinism rate, obligation tracking)
- Integration with Phase 1 (lowering, compilation) and Phase 2 (execution)

Exports:
    Main runner function and validators
"""

from .phase3 import (
    # Constants
    N, PAGE_SIZE, PAGES,
    
    # Phase 1 subset
    tokenize, parse_stmt, lower, Policies, admissible,
    compile_words, compile_program, pretty_print_program,
    
    # Phase 2 subset
    rotate_Rk, projector_A, projector_Delta,
    make_ring_graph, edges_of, from_edges,
    permute_nodes, rotate_graph, quotient_graph_mod,
    exec_program,
    
    # Phase 3 — Unit properties
    unit_projector_idempotence,
    witness_perm_q,
    unit_noncommutation_witness,
    unit_rotation_closure,
    unit_split_merge_roundtrip,
    
    # Round-trip test
    roundtrip_check,
    
    # KPIs
    determinism_rate,
    obligation_counts,
    
    # Main runner
    main,
)

__all__ = [
    # Constants
    'N', 'PAGE_SIZE', 'PAGES',
    
    # Phase 1 subset
    'tokenize', 'parse_stmt', 'lower', 'Policies', 'admissible',
    'compile_words', 'compile_program', 'pretty_print_program',
    
    # Phase 2 subset
    'rotate_Rk', 'projector_A', 'projector_Delta',
    'make_ring_graph', 'edges_of', 'from_edges',
    'permute_nodes', 'rotate_graph', 'quotient_graph_mod',
    'exec_program',
    
    # Phase 3 — Unit properties
    'unit_projector_idempotence',
    'witness_perm_q',
    'unit_noncommutation_witness',
    'unit_rotation_closure',
    'unit_split_merge_roundtrip',
    
    # Round-trip test
    'roundtrip_check',
    
    # KPIs
    'determinism_rate',
    'obligation_counts',
    
    # Main runner
    'main',
]
