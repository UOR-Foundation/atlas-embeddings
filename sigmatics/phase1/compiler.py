"""
Sigmatics to Multiplicity Compiler

This module compiles lowered Sigmatics words to Multiplicity words with:
1. Π-first reduction (projectors processed first)
2. Admissibility checks (p^r | n)
3. Obligation tracking for UNPROVEN policies

The compiler ensures all projectors are placed first in the word sequence
for optimal execution in the Multiplicity runtime.
"""

from typing import List, Dict, Any, Tuple

try:
    from .policies import Policies, admissible, N
except ImportError:
    from policies import Policies, admissible, N


def compile_words(
    sig_words: List[Dict[str, Any]], 
    policies: Policies
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Compile Sigmatics words to Multiplicity words with Π-first reduction.
    
    Pipeline:
    1. Process each Sigmatics word
    2. Separate projectors (Π-atoms) from other operations
    3. Apply policies for unspecified parameters
    4. Check admissibility constraints
    5. Track obligations for UNPROVEN policies
    6. Return projectors first, then other operations
    
    Args:
        sig_words: List of lowered Sigmatics words
        policies: Policies object for prime/level/perm selection
        
    Returns:
        Tuple of (compiled_words, obligations)
        - compiled_words: Multiplicity words with projectors first
        - obligations: List of obligation dictionaries tracking UNPROVEN items
        
    Raises:
        ValueError: If admissibility check fails
    """
    projectors: List[Dict[str, Any]] = []
    others: List[Dict[str, Any]] = []
    obligations: List[Dict[str, Any]] = []
    
    for w in sig_words:
        op = w["op"]
        args = w.get("args", {})
        
        if op == "copy":
            others.append({"op": "copy"})
            
        elif op == "mirror" or op == "swap" or (op == "control" and args.get("kind") == "mu"):
            # These operations require permutation policy
            ctx = {"op": op, **args}
            pi = policies.permPolicy(ctx, N)
            
            # Track obligation for UNPROVEN policy
            obligations.append({
                "type": "policy",
                "name": "permPolicy",
                "status": "UNPROVEN",
                "ctx": ctx
            })
            
            others.append({
                "op": "permute",
                "pi": pi,
                "note": "UNPROVEN policy"
            })
            
        elif op == "merge":
            ar = policies.arityPolicy(args)
            
            obligations.append({
                "type": "policy",
                "name": "arityPolicy",
                "status": "UNPROVEN",
                "arity": ar
            })
            
            others.append({
                "op": "merge",
                "arity": ar
            })
            
        elif op == "split":
            ellType = args.get("ellType", "unknown")
            others.append({
                "op": "split",
                "ellType": ellType
            })
            
        elif op == "mark":
            # mark@{...} creates a projector (Π-atom)
            d = args.get("d", {})
            p = policies.primePolicy(d)
            r = policies.levelPolicy(d)
            
            # Check admissibility: p^r must divide n
            if not admissible(p, r, N):
                obligations.append({
                    "type": "admissibility",
                    "p": p,
                    "r": r,
                    "n": N,
                    "status": "VIOLATION"
                })
                raise ValueError(
                    f"Admissibility failed: p^r={p}^{r} does not divide n={N}"
                )
            
            mode = policies.markMode(d)
            
            obligations.append({
                "type": "policy",
                "name": "primePolicy/levelPolicy/markMode",
                "status": "UNPROVEN",
                "p": p,
                "r": r,
                "mode": mode
            })
            
            # Projectors go to the front (Π-first)
            projectors.append({
                "op": "projector",
                "p": p,
                "r": r,
                "mode": mode,
                "note": "UNPROVEN policy"
            })
            
        elif op == "quote":
            others.append({
                "op": "modal_enter",
                "note": "UNPROVEN semantics"
            })
            obligations.append({
                "type": "semantics",
                "name": "quote",
                "status": "UNPROVEN"
            })
            
        elif op == "evaluate":
            others.append({
                "op": "modal_exit",
                "note": "UNPROVEN semantics"
            })
            obligations.append({
                "type": "semantics",
                "name": "evaluate",
                "status": "UNPROVEN"
            })
            
        elif op == "control" and args.get("kind") in ("rho", "tau"):
            # rho[k] or tau[k] - rotation operations
            k = int(args.get("k", 0))
            if args["kind"] == "tau":
                k = -k  # tau is negative rotation
            
            others.append({
                "op": "rotate",
                "k": k
            })
            
        else:
            raise ValueError(f"Unsupported op in compiler: {op}")
    
    # Π-first reduction: projectors first, then others
    prog = projectors + others
    return prog, obligations


def compile_program(
    lowered: Dict[str, Any], 
    policies: Policies
) -> Dict[str, Any]:
    """
    Compile a complete lowered Sigmatics program to a Multiplicity program.
    
    Args:
        lowered: Lowered Sigmatics program (from lowering.lower())
        policies: Policies object
        
    Returns:
        Multiplicity program dictionary with:
          - "n": Index size
          - "words": Compiled Multiplicity words (Π-first)
          - "obligations": List of tracked obligations
    """
    sig_words = lowered["words"]
    words, obligations = compile_words(sig_words, policies)
    
    return {
        "n": N,
        "words": words,
        "obligations": obligations
    }
