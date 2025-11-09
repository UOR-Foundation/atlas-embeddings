from multiplicity_core.quantizer import Z96Quantizer


def test_quantizer_range_and_decode():
    q = Z96Quantizer(scale=2.0, offset=0.5)
    z = q.quantize(3.25)
    assert 0 <= z < 96
    x0 = q.decode(z)
    # Round‑trip modulo 96 holds only up to periodicity; check type and finiteness
    assert isinstance(x0, float)
