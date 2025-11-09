from atlas12288.symmetry import Involutions


def test_involutions_commute_and_square():
    for p0 in (0, 7, 8, 15, 16, 31, 40, 47):
        for b0 in (0, 1, 2, 127, 128, 255):
            # Square to identity
            for j in range(11):
                p, b = Involutions.apply(p0, b0, j)
                p2, b2 = Involutions.apply(p, b, j)
                assert p2 % 48 == p0 % 48 and b2 % 256 == b0 % 256
            # Commute pairwise
            for i in range(11):
                for j in range(11):
                    pA, bA = Involutions.apply(Involutions.apply(p0, b0, i)[0], Involutions.apply(p0, b0, i)[1], j)
                    pB, bB = Involutions.apply(Involutions.apply(p0, b0, j)[0], Involutions.apply(p0, b0, j)[1], i)
                    assert (pA % 48, bA % 256) == (pB % 48, bB % 256)
