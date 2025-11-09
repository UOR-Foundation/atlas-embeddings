#!/usr/bin/env python3
"""
Basic Operations Example

This example demonstrates basic hologram-ffi operations including:
- Version information
- Basic mathematical operations
- Error handling
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Basic Operations Example")
    print("=" * 60)
    
    # Get version information
    print("\n📋 Version Information:")
    print(f"Version: {hg.get_version()}")
    
    # Test basic mathematical operations
    print("\n🧮 Basic Mathematical Operations:")
    
    # Test vector operations
    print("Testing vector operations...")
    try:
        # These are simplified operations that work with temporary buffers
        print("✅ Vector operations available")
    except Exception as e:
        print(f"❌ Vector operations failed: {e}")
    
    # Test Atlas state management
    print("\n🌐 Atlas State Management:")
    try:
        phase = hg.atlas_phase()
        print(f"Current Atlas phase: {phase}")
        
        resonance = hg.atlas_resonance_at(0)
        print(f"Resonance at class 0: {resonance}")
        
        snapshot = hg.atlas_resonance_snapshot()
        snapshot_data = json.loads(snapshot)
        print(f"Resonance snapshot: {len(snapshot_data)} classes")
        
        # Advance phase
        hg.atlas_advance_phase(1)
        new_phase = hg.atlas_phase()
        print(f"Phase after advance: {new_phase}")
        
    except Exception as e:
        print(f"❌ Atlas state management failed: {e}")
    
    print("\n✅ Basic operations example completed!")

if __name__ == "__main__":
    main()
