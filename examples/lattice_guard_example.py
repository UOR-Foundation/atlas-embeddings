#!/usr/bin/env python
"""
Example demonstrating the complete lattice guard and audit workflow.

This script shows how to:
1. Generate the subgroup certificate
2. Use lattice_guard to validate step contexts
3. Create a ledger with proper PETC entries
4. Run the audit to verify fairness and compliance
"""
from __future__ import annotations

import json
from pathlib import Path

from multiplicity_core.boundary_lattice import save_certificate, CLASSES, ANCHORS
from multiplicity_core.lattice_guard import guard_context
from multiplicity_core.ledger import Ledger
from multiplicity_core.audit_runner import audit, load_toml


def main():
    print("=" * 60)
    print("Atlas Boundary Lattice Guard Example")
    print("=" * 60)
    
    # Step 1: Generate subgroup certificate
    print("\n1. Generating (Z/2)^11 subgroup certificate...")
    cert_path = "example_subgroup_certificate.json"
    save_certificate(cert_path)
    print(f"   ✓ Certificate written to {cert_path}")
    
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    print(f"   ✓ Verification status: {cert['verification']['verified']}")
    print(f"   ✓ Group structure: {cert['group_structure']}")
    print(f"   ✓ Total elements: {cert['properties']['total_elements']}")
    
    # Step 2: Demonstrate lattice guard usage
    print("\n2. Demonstrating lattice guard...")
    
    # Example with coord
    ctx1 = {"class": 5, "coord": 777}
    guarded1 = guard_context(ctx1)
    print(f"   Input:  class={ctx1['class']}, coord={ctx1['coord']}")
    print(f"   Output: anchor={guarded1['anchor']}, v_bits={guarded1['v_bits']}, row={guarded1['row']}, col={guarded1['col']}")
    
    # Example with anchor and v_bits
    ctx2 = {"class": 10, "anchor": 2, "v_bits": 100}
    guarded2 = guard_context(ctx2)
    print(f"   Input:  class={ctx2['class']}, anchor={ctx2['anchor']}, v_bits={ctx2['v_bits']}")
    print(f"   Output: coord={guarded2['coord']}, row={guarded2['row']}, col={guarded2['col']}")
    
    # Step 3: Create a ledger with guarded contexts
    print("\n3. Creating ledger with guarded contexts...")
    ledger = Ledger()
    
    # Simulate 768 steps with fair distribution
    steps = 768
    for step in range(steps):
        c = step % CLASSES
        a = step % ANCHORS
        
        # Guard the context
        ctx = {"class": c, "anchor": a, "v_bits": step % 256}
        guarded_ctx = guard_context(ctx)
        
        # Add ACE step entry
        ace_entry = {
            "kind": "ace_step",
            "status": "committed",
            "context": guarded_ctx,
            "t": step
        }
        entry_id = ledger.append(ace_entry)
        
        # Add PETC entry referencing the ACE step
        petc_entry = {
            "kind": "petc",
            "context": {"ace": entry_id},
            "t": step
        }
        ledger.append(petc_entry)
        
        # Add audit entry every 768 steps
        if (step + 1) % 768 == 0:
            audit_entry = {
                "kind": "audit",
                "t": step + 1
            }
            ledger.append(audit_entry)
    
    print(f"   ✓ Created {len(ledger.entries)} ledger entries")
    
    # Save ledger
    ledger_path = "example_ledger.json"
    with open(ledger_path, 'w') as f:
        json.dump(ledger.entries, f, indent=2)
    print(f"   ✓ Ledger written to {ledger_path}")
    
    # Step 4: Run audit
    print("\n4. Running audit...")
    
    # Load configuration
    schedule = {
        "n_classes": CLASSES,
        "n_anchors": ANCHORS,
        "n_columns": 768
    }
    
    bundle_path = "multiplicity_core/audit_bundle.toml"
    bundle = load_toml(bundle_path)
    
    # Run audit
    report = audit(ledger.entries, schedule, bundle)
    
    print(f"   ✓ Total steps audited: {report['total_steps']}")
    print(f"   ✓ Fair classes: {report['fair_classes_ok']}")
    print(f"   ✓ Fair anchors: {report['fair_anchors_ok']}")
    print(f"   ✓ Missing PETC entries: {len(report['missing_petc'])}")
    print(f"   ✓ Audit interval compliance: {report['audit_ok']}")
    print(f"   ✓ Audit entries found: {report['audit_entries']}")
    
    # Save audit report
    report_path = "example_audit_report.json"
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2)
    print(f"   ✓ Audit report written to {report_path}")
    
    # Summary
    print("\n" + "=" * 60)
    print("Summary")
    print("=" * 60)
    all_ok = (
        report['fair_classes_ok'] and 
        report['fair_anchors_ok'] and 
        len(report['missing_petc']) == 0 and
        report['audit_ok']
    )
    
    if all_ok:
        print("✓ All checks passed! The ledger is compliant.")
    else:
        print("✗ Some checks failed. Review the audit report.")
    
    print("\nGenerated files:")
    print(f"  - {cert_path}")
    print(f"  - {ledger_path}")
    print(f"  - {report_path}")
    print("\nTo run audit manually:")
    print(f"  python -m multiplicity_core.audit_runner --ledger {ledger_path} --schedule atlas_schedule.toml --bundle {bundle_path}")


if __name__ == "__main__":
    main()
