#!/usr/bin/env python3
"""
Example Sigma plugin for sovereignty_gate AEP
Contract: sigma(actor_id: str, t_ms: int) -> int in {0,1}
Replace with your identity/sovereignty policy.
"""


def sigma(actor_id: str, t_ms: int) -> int:
    """
    Demo: only 'alice' is sovereign.
    
    Args:
        actor_id: The identity requesting access
        t_ms: Timestamp in milliseconds
        
    Returns:
        1 if identity is sovereign, 0 otherwise
    """
    # Demo: only 'alice' is sovereign
    return 1 if actor_id == "alice" else 0
