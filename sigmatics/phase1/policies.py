"""
Policies and Admissibility Checks

This module defines the default policies for prime selection, level selection,
and permutation generation. All policies are marked UNPROVEN until mathematically
verified.

Default policies:
- primePolicy(d) → p: Default p=3
- levelPolicy(d) → r: Default r=1
- permPolicy(ctx, n) → π: Default identity permutation
- arityPolicy(ctx) → int: Default arity 2
- markMode(d) → str: Default "Δ" (delta)
"""

from typing import Dict, Any, List

# Fixed index size from Phase 0
N = 12288


class Policies:
    """
    Policy functions for compilation.
    
    All policies are UNPROVEN and serve as defaults.
    They should be replaced with verified implementations.
    """
    
    @staticmethod
    def primePolicy(d: Dict[str, Any]) -> int:
        """
        Select prime p for a modality dictionary.
        
        UNPROVEN: Default p=3 for all modalities.
        
        Args:
            d: Modality dictionary (from mark@{...})
            
        Returns:
            Prime p (default: 3)
        """
        return d.get("p", 3)
    
    @staticmethod
    def levelPolicy(d: Dict[str, Any]) -> int:
        """
        Select level r for a modality dictionary.
        
        UNPROVEN: Default r=1 for all modalities.
        
        Args:
            d: Modality dictionary (from mark@{...})
            
        Returns:
            Level r (default: 1)
        """
        return d.get("r", 1)
    
    @staticmethod
    def permPolicy(ctx: Dict[str, Any], n: int) -> List[int]:
        """
        Generate permutation π for a context.
        
        UNPROVEN: Default identity permutation.
        May look at ctx for "swap", "mirror", "mu" operations.
        
        Args:
            ctx: Operation context dictionary
            n: Index size
            
        Returns:
            Permutation as list of indices (default: identity)
        """
        return list(range(n))
    
    @staticmethod
    def arityPolicy(ctx: Dict[str, Any]) -> int:
        """
        Select arity for merge/split operations.
        
        UNPROVEN: Default arity 2.
        
        Args:
            ctx: Operation context dictionary
            
        Returns:
            Arity (default: 2)
        """
        return int(ctx.get("arity", 2))
    
    @staticmethod
    def markMode(d: Dict[str, Any]) -> str:
        """
        Select mode for mark operation.
        
        UNPROVEN: Choose "Δ" (delta) unless explicitly "A".
        
        Args:
            d: Modality dictionary (from mark@{...})
            
        Returns:
            Mode string: "Δ" or "A"
        """
        mode = d.get("mode", "Δ")
        return "A" if mode == "A" else "Δ"


def admissible(p: int, r: int, n: int = N) -> bool:
    """
    Check projector admissibility: p^r must divide n.
    
    This is a hard constraint from Phase 0.
    For n = 12,288 = 2^12 × 3^1:
    - Admissible: (2,1..12), (3,1)
    - Not admissible: (5,1), (2,13), (3,2), etc.
    
    Args:
        p: Prime
        r: Level
        n: Index size (default: 12,288)
        
    Returns:
        True if p^r divides n, False otherwise
    """
    return (n % (p ** r)) == 0
