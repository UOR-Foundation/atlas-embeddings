import pytest

pytestmark = pytest.mark.skip(reason="property stubs; implement per schedule fairness and CNF")

def test_schedule_fairness_empirical():
    # TODO: collect visit counts; run DKW/SPRT; BY option when dependent
    assert True
