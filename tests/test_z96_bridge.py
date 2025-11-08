from atlas12288.z96_bridge import classify_byte_mod96, z96_distribution, heavy_vs_light_classes
from multiplicity_core.quantizer import Z96Quantizer


def test_python_z96_matches_mod96_and_quantizer():
    q = Z96Quantizer(scale=1.0, offset=0.0)
    for b in range(256):
        assert classify_byte_mod96(b) == (b % 96)
        assert classify_byte_mod96(b) == q.quantize(b)


def test_256_to_96_distribution_counts():
    dist = z96_distribution()
    assert sum(dist.values()) == 256
    heavy = [k for k, v in dist.items() if v == 3]
    light = [k for k, v in dist.items() if v == 2]
    assert len(heavy) == 64 and len(light) == 32
    # First 64 residues [0..63] are the heavy ones for 0..255 mapping
    assert set(heavy) == set(range(64))
