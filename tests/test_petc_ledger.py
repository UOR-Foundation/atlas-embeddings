from multiplicity_core.petc import PETCLedger


def test_petc_chain_happy_path():
    L = PETCLedger()
    L.append("op1", {"a": 1})
    L.append("op2", {"b": [1, 2, 3]})
    assert L.verify()
