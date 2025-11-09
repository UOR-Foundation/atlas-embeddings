from atlas12288.anchors import ANCHORS

def test_six_anchors_are_8m_0():
    assert len(ANCHORS) == 6
    for m, ab in enumerate(ANCHORS):
        assert ab == ((8 * m) % 48, 0)
